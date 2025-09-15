using PlanRecognitionNETF;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;

namespace PlanRecognitionExtension
{
    internal class TIHTNPlanner : EarleyPlanner
    { 
        const string WS_ROOT_DIR = "TIHTN";
        readonly string workingDirectory = Path.Combine(WS_ROOT_DIR, DateTime.Now.Ticks.ToString());
        List<ActionType> actionsOutsideHierarchy = new();
        Dictionary<string, List<Term>> posEffectsOfActionsOutsideHierarchy = new();
        Dictionary<string, List<Term>> negEffectsOfActionsOutsideHierarchy = new();
        List<Term> allPredicates;
        List<Rule> allRules;
        const string TIHTN_ACTION_NAME_SUFFIX = "_tihtn_action";
        const string TIHTN_ACTION_EFFECT_NAME = "tihtn_effect";
        readonly string CLASSICAL_PLANNER;
        const string PYTHON = @"python";
        const string PLANNER_PARAMETERS = "--search \"astar(lmcut())\"";
        const string DOMAIN_NAME = "d";
        const string PROBLEM_NAME = "p";
        const string DOMAIN_FILE_NAME = "domain.pddl";
        const string PROBLEM_FILE_NAME = "problem.pddl";
        const string PLAN_FILE_NAME = "sas_plan";
        TaskInsertionMode TASK_INSERTION_MODE { get; }

        public TIHTNPlanner(string classicalPlannerPath, List<TaskType> allTaskTypes, List<ActionType> allActionTypes, List<Constant> allConstants, 
            List<ConstantType> allConstantTypes, List<Term> initialState, List<Task> toGoals,
            List<Term> allPredicates, List<Rule> allRules,
            bool actionInsertionAllowed = true, 
            bool actionDeletionAllowed = false, bool anytimeGoals = true,
            bool returnFirstResult = true, TaskInsertionMode taskInsertionMode = TaskInsertionMode.InsertOnTheFly) : base(allTaskTypes, allActionTypes, allConstants, allConstantTypes, initialState, toGoals, 
                actionInsertionAllowed, actionDeletionAllowed, anytimeGoals, returnFirstResult)
        {
            this.allPredicates = allPredicates;
            this.allRules = allRules;
            FindActionsOutsideHierarchy();
            FindEffectsOfActionsOutsideHierarchy();
            InitializeTIHTNws();
            TASK_INSERTION_MODE = taskInsertionMode;
            CLASSICAL_PLANNER = classicalPlannerPath;

            if (TASK_INSERTION_MODE == TaskInsertionMode.InsertOnTheFly)
            {
                RETURN_FIRST_SOLUTION = true;
                ANYTIME_GOALS = true;
            }
            else
            {
                ANYTIME_GOALS = true;
                RETURN_FIRST_SOLUTION = returnFirstResult;
            }

            Console.WriteLine("TIHTN planner settings:");
            Console.WriteLine($"  Task insertion mode: {TASK_INSERTION_MODE}");
            Console.WriteLine($"  Anytime goals: {ANYTIME_GOALS}");
            Console.WriteLine($"  Return first solution: {RETURN_FIRST_SOLUTION}");
        }

        void FindEffectsOfActionsOutsideHierarchy()
        {
            foreach (var action in actionsOutsideHierarchy)
            {
                foreach (var effect in action.PosPostConditions)
                {
                    Term effectTerm = new Term(effect.Item1, effect.Item2.Select(i => 
                    !action.ActionTerm.Variables[i].Name.StartsWith('?')?action.ActionTerm.Variables[i]:
                    new Constant(null, action.ActionTerm.Variables[i].Type)).ToArray());
                    if (!posEffectsOfActionsOutsideHierarchy.ContainsKey(effectTerm.Name))
                    {
                        posEffectsOfActionsOutsideHierarchy.Add(effectTerm.Name, new());
                    }
                    posEffectsOfActionsOutsideHierarchy[effectTerm.Name].Add(effectTerm);
                }

                foreach (var effect in action.NegPostConditions)
                {
                    Term effectTerm = new Term(effect.Item1, effect.Item2.Select(i =>
                                        !action.ActionTerm.Variables[i].Name.StartsWith('?') ? action.ActionTerm.Variables[i] :
                                        new Constant(null, action.ActionTerm.Variables[i].Type)).ToArray());
                    if (!negEffectsOfActionsOutsideHierarchy.ContainsKey(effectTerm.Name))
                    {
                        negEffectsOfActionsOutsideHierarchy.Add(effectTerm.Name, new());
                    }
                    negEffectsOfActionsOutsideHierarchy[effectTerm.Name].Add(effectTerm);
                }
            }
        }

        void FindActionsOutsideHierarchy()
        {
            HashSet<ActionType> actionTypesInHierarchy = new();
            foreach (var rule in allRules)
            {
                foreach (var subtask in rule.TaskTypeArray)
                {
                    ActionType correspondingActionType = InputReader.FindActionType(AllActionTypes, subtask.Name, subtask.NumOfVariables);
                    if (correspondingActionType != null)
                    {
                        actionTypesInHierarchy.Add(correspondingActionType);
                    }
                }
            }

            foreach (var actionType in AllActionTypes)
            {
                if (!actionTypesInHierarchy.Contains(actionType))
                {
                    actionsOutsideHierarchy.Add(actionType);
                    TaskType taskType = new(actionType.ActionTerm.Name, actionType.ActionTerm.Variables.Length);
                    actionType.TaskType = taskType;
                    AllTaskTypes.Add(taskType);
                }
            }
        }

        protected override bool IsApplicableToCurrentState(Subplan action, 
            out List<Subplan> actionsToInsert, out List<Action> correspondingActions, 
            int timelinePosition, 
            out List<Term> unsatisfiedPosPreconditions, out List<Term> unsatisfiedNegPreconditions)
        {
            switch (TASK_INSERTION_MODE)
            {
                case TaskInsertionMode.InsertOnTheFly:

                    if (base.IsApplicableToCurrentState(action, out actionsToInsert,
                        out correspondingActions, timelinePosition, 
                        out unsatisfiedPosPreconditions, out unsatisfiedNegPreconditions))
                    {
                        return true;
                    }
                    else if (PreconditionsCanBeSatisfiedByClassicalPlan(unsatisfiedPosPreconditions,
                        unsatisfiedNegPreconditions) &&
                        FindActionSequenceUsingClassicalPlanner(action.Timeline[0].PosPreConditions,
                        action.Timeline[0].NegPreConditions, 
                        out List<Subplan> newActionsToInsert, out var newCorrespondingActions, 
                        CurrentPlan.Count, CurrentPlan.Count))
                    {
                        actionsToInsert = newActionsToInsert;
                        actionsToInsert.Add(action);
                        correspondingActions = newCorrespondingActions;
                        newCorrespondingActions.Add(new Action(
                            InputReader.FindActionType(AllActionTypes, action.TaskType.Name, 
                            action.TaskType.NumOfVariables),
                            action.TaskInstance.Variables));
                        unsatisfiedNegPreconditions.Clear();
                        unsatisfiedPosPreconditions.Clear();
                        return true;
                    }

                    return false;

                case TaskInsertionMode.InsertAllAtOnce:
                    if (base.IsApplicableToCurrentState(action, out actionsToInsert,
                        out correspondingActions, timelinePosition,
                        out unsatisfiedPosPreconditions, out unsatisfiedNegPreconditions)
                        || PreconditionsCanBeSatisfiedByClassicalPlan(unsatisfiedPosPreconditions,
                        unsatisfiedNegPreconditions))
                    {
                        actionsToInsert = new()
                    {
                        action
                    };
                        correspondingActions = new()
                    {
                        new Action(InputReader.FindActionType(AllActionTypes, action.TaskType.Name,
                        action.TaskType.NumOfVariables))
                    };
                        unsatisfiedPosPreconditions = new();
                        unsatisfiedNegPreconditions = new();
                        return true;
                    }
                    else
                    {
                        return false;
                    }
                default:
                    throw new NotSupportedException();
            }
        }

        private bool PreconditionsCanBeSatisfiedByClassicalPlan(List<Term> unsatisfiedPosPreconditions, 
            List<Term> unsatisfiedNegPreconditions)
        {
            foreach (var precond in unsatisfiedPosPreconditions)
            {
                bool found = false;
                if (posEffectsOfActionsOutsideHierarchy.TryGetValue(precond.Name, out var effects))
                {
                    foreach (var effect in effects)
                    {
                        if (NonConflictingInstantiations(effect.Variables, precond.Variables))
                        {   
                            found = true; 
                            break;
                        }
                    }
                }

                if (!found)
                {
                    return false;
                }
            }

            foreach (var precond in unsatisfiedNegPreconditions)
            {
                bool found = false;
                if (negEffectsOfActionsOutsideHierarchy.TryGetValue(precond.Name, out var effects))
                {
                    foreach (var effect in effects)
                    {
                        if (NonConflictingInstantiations(precond.Variables, effect.Variables))
                        {
                            found = true;
                            break;
                        }
                    }
                }

                if (!found)
                {
                    return false;
                }
            }

            return true;
        }

        private bool FindActionSequenceUsingClassicalPlanner(List<Term> posPreconditions, 
            List<Term> negPreconditions,
            out List<Subplan> newActionsToInsert, out List<Action> correspondingActions,
            int startIndex, int actionInsertionPosition = -1)
        {
            posPreconditions = posPreconditions.GroupBy(x => x).Select(x => x.First()).ToList();
            negPreconditions = negPreconditions.GroupBy(x => x).Select(x => x.First()).ToList();
            string currentDirectory = Path.Combine(workingDirectory, DateTime.Now.Ticks.ToString());
            Directory.CreateDirectory(currentDirectory);
            File.Copy(Path.Combine(workingDirectory, DOMAIN_FILE_NAME), Path.Combine(currentDirectory, 
                DOMAIN_FILE_NAME));
            DefinePDDLProblemBasedOnPreconditions(currentDirectory, posPreconditions, negPreconditions, 
                actionInsertionPosition);

#if DEBUG
            Console.WriteLine("Calling planner for preconditions " + 
                string.Join(", ", posPreconditions.Select(x => x.ToString())));
#endif

            CallClassicalPlanner(currentDirectory);

            if (File.Exists(Path.Combine(currentDirectory, PLAN_FILE_NAME)))
            {
                newActionsToInsert = ProcessClassicalPlan(currentDirectory, startIndex, 
                    out correspondingActions);

                return true;
            }
            else
            {
                newActionsToInsert = null;
                correspondingActions = null;
                return false;
            }
        }

        private List<Subplan> ProcessClassicalPlan(string currentDirectory, int startIndex,
            out List<Action> correspondingActions)
        {
            using StreamReader sr = new StreamReader(Path.Combine(currentDirectory, PLAN_FILE_NAME));
            List<Subplan> result = new();
            correspondingActions = new List<Action>();
            string line;
            int actionIndex = startIndex;
            while ((line = sr.ReadLine()?.Trim()) != null)
            {
                if (line.Length > 0 && !line.StartsWith(';'))
                {
                    result.Add(ProcessAction(line, startIndex++, out Action action));
                    correspondingActions.Add(action);
                }
            }

            return result;
        }

        private Subplan ProcessAction(string line, int startIndex, out Action action)
        {
            line = line.Replace(")", "").Replace("(", "").Trim();
            string[] items = line.Split(' ', 
                StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries);
            string actionName = items[0];
            Constant[] actionVariables = items[1..].Select(x => InputReader.FindConstant(x, AllConstants))
                .ToArray();
            ActionType actionType = InputReader.FindActionType(AllActionTypes, actionName, 
                actionVariables.Length);
            TaskType taskType;
            if (actionType == null)
            {
                taskType = new TaskType(actionName, actionVariables.Length);
            }
            else
            {
                taskType = FindTaskType(actionType.ActionTerm, AllTaskTypes);
            }
            action = new(actionType, actionVariables);
            Subplan subplan = new Subplan(new(actionName, actionVariables), startIndex, startIndex, taskType);
            Slot slot = CreateConditionsSlot(subplan, AllActionTypes, AllConstants);
            subplan.usedActions = Array.Empty<bool>();
            subplan.SetSlot(0, slot);

            return subplan;
        }

        private void CallClassicalPlanner(string currentDirectory)
        {
            Process process = new()
            {
                StartInfo = new ProcessStartInfo(PYTHON, CLASSICAL_PLANNER + " " + PROBLEM_FILE_NAME + 
                " " + PLANNER_PARAMETERS)
                {
                    RedirectStandardOutput = true,
                    UseShellExecute = false,
                    CreateNoWindow = true,
                    RedirectStandardError = true,
                    WorkingDirectory = currentDirectory
                }
            };

            process.Start();
            string output = process.StandardOutput.ReadToEnd();
            string error = process.StandardError.ReadToEnd();
            process.WaitForExit();
            ProcessOutput(output, error, currentDirectory);
        }

        private void ProcessOutput(string output, string error, string currentDirectory)
        {
            using StreamWriter sw = new StreamWriter(Path.Combine(currentDirectory, "downward_output.txt"));
            sw.WriteLine(output);
            sw.WriteLine("---ERROR OUTPUT---");
            sw.WriteLine(error);
        }

        List<string> DefineInitialState(HashSet<Constant> allUsedConstants, 
            int actionInsertionPosition = -1)
        {
            List<Term> previousSlot;

            switch (TASK_INSERTION_MODE)
            {
                case TaskInsertionMode.InsertOnTheFly:
                    previousSlot = GetLastSlotConditions(actionInsertionPosition);
                    break;
                case TaskInsertionMode.InsertAllAtOnce:
                    previousSlot = InitialState;
                    break;
                default:
                    throw new NotSupportedException();
            }
            
            HashSet<Constant> usedConstants = new();
            List<string> termsList = new();
            foreach (Term term in previousSlot)
            {
                string termString = $"{term.Name} {string.Join(' ', term.Variables.Select(x => x.Name))}";
                if (termString.Trim() != ":init")
                {
                    termsList.Add(termString);
                    usedConstants.UnionWith(term.Variables);
                }
            }

            List<string> result = new();
            foreach (var constant in usedConstants)
            {
                foreach (var constantType in constant.Type.AncestorTypes)
                {
                    result.Add($"{constantType.Name} {constant.Name}");
                }
            }

            result.AddRange(termsList);
            allUsedConstants.UnionWith(usedConstants);
            return result.GroupBy(x => x).Select(x => x.First()).ToList();
        }

        void DefinePDDLProblemBasedOnAction(string currentDirectory, Subplan action)
        {
            DefinePDDLProblem(currentDirectory, action.Timeline[0].PosPreConditions, 
                action.Timeline[0].NegPreConditions, null);
        }

        void DefineCompletePDDLProblem(string currentDirectory, string goal)
        {
            DefinePDDLProblem(currentDirectory, null, null, goal);
        }

        void DefinePDDLProblemBasedOnPreconditions(string currentDirectory, List<Term> posPreconditions,
            List<Term> negPreconditions, int actionInsertionPosition = -1)
        {
            DefinePDDLProblem(currentDirectory, posPreconditions, negPreconditions,
                null, actionInsertionPosition);
        }

        private void DefinePDDLProblem(string currentDirectory, List<Term> posPreconditions,
            List<Term> negPreconditions, string goal, int actionInsertionPosition = -1)
        {
            HashSet<Constant> usedConstants = new(); 
            List<string> initStateStrings = DefineInitialState(usedConstants, actionInsertionPosition);
            List<string> goalStrings;

            if (goal == null)
            {
                goalStrings = DefineGoal(posPreconditions, negPreconditions, usedConstants);
            }
            else
            {
                goalStrings = new() { goal };
            }

            using (StreamWriter sw = new(Path.Combine(currentDirectory, PROBLEM_FILE_NAME)))
            {
                sw.WriteLine($"(define (problem {PROBLEM_NAME})");
                sw.WriteLine($"  (:domain {DOMAIN_NAME})");
                sw.WriteLine($"(:objects {string.Join(' ', AllConstants.Select(x => x.Name))})");
                sw.WriteLine();
                sw.WriteLine("(:init");
                foreach (var initTerm in initStateStrings)
                {
                    sw.WriteLine($"({initTerm})");
                }
                sw.WriteLine(")");
                sw.WriteLine();
                sw.WriteLine("(:goal (and");
                foreach (var goalTerm in goalStrings)
                {
                    sw.WriteLine($"({goalTerm})");
                }
                sw.WriteLine("))");
                sw.WriteLine(")");
            }
        }

        private List<string> DefineGoal(List<Term> posPreconditions, List<Term> negPreconditions, 
            HashSet<Constant> allUsedConstants)
        {
            List<string> goalStrings = new();
            HashSet<Constant> usedConstants = new(); 
            foreach (var precond in posPreconditions)
            {
                goalStrings.Add($"{precond.Name} {string.Join(' ', precond.Variables.Select(x => x.Name))}");
                usedConstants.UnionWith(precond.Variables);
            }
            foreach (var precond in negPreconditions)
            {
                goalStrings.Add($"not ({precond.Name} {string.Join(' ', precond.Variables.Select(x => x.Name))})");
                usedConstants.UnionWith(precond.Variables);
            }

            List<string> result = new();
            foreach (var constant in usedConstants)
            {
                result.Add($"{constant.Type.Name} {constant.Name}");
            }

            result.AddRange(goalStrings);
            allUsedConstants.UnionWith(usedConstants);
            return result;
        }

        void InitializeTIHTNws()
        {
            if (!Directory.Exists(WS_ROOT_DIR))
            {
                Directory.CreateDirectory(WS_ROOT_DIR);
            }

            Directory.CreateDirectory(workingDirectory);

            DefinePDDLDomain();
        }


        internal override bool MegaslotPropagate(ref List<Slot> timeline, int prefixTimelineLength, int startIndex)
        {
            switch (TASK_INSERTION_MODE)
            {
                case TaskInsertionMode.InsertOnTheFly:
                    List<Slot> newTimeline = new();
                    newTimeline.AddRange(CurrentTimeline);
                    return base.MegaslotPropagate(ref newTimeline, 0, -1);

                case TaskInsertionMode.InsertAllAtOnce:
                    return true; // constraint checking performed at the end

                default:
                    throw new NotSupportedException();
            }
        }

        protected override bool ApplyConditionsAndCheckValidity(Subplan subplan, RuleInstance ruleInstance, List<Subplan> subtasks, EarleyParser parser, int indexToCheckPreconditionsFrom = 0)
        {
            switch (TASK_INSERTION_MODE)
            {
                case TaskInsertionMode.InsertOnTheFly:
                    return base.ApplyConditionsAndCheckValidity(subplan, ruleInstance, subtasks, parser, indexToCheckPreconditionsFrom);
                case TaskInsertionMode.InsertAllAtOnce:
                    return true; // checked at the end
                default:
                    throw new NotSupportedException();
            }
        }

        protected override bool CheckWholeTimeline(out List<ActionSubplan> newCurrentPlan)
        {
            switch (TASK_INSERTION_MODE)
            {
                case TaskInsertionMode.InsertOnTheFly:
                    newCurrentPlan = CurrentPlan;
                    return true;
                case TaskInsertionMode.InsertAllAtOnce:
                    List<Slot> newTimeline = new();
                    newTimeline.AddRange(CurrentTimeline);
                    if (IsCurrentPlanApplicableInInitialState() && base.MegaslotPropagate(ref newTimeline, 0, -1))
                    {
                        newCurrentPlan = CurrentPlan;
                        return true;
                    }
                    else
                    {
                        List<NewGroundAction> newActions = CreateNewActions(out List<Term> newPredicates);
                        string currentDirectory = Path.Combine(workingDirectory, DateTime.Now.Ticks.ToString());
                        Directory.CreateDirectory(currentDirectory);
                        DefinePDDLDomain(newPredicates, newActions, currentDirectory);
                        DefineCompletePDDLProblem(currentDirectory, newPredicates[^1].Name);
#if DEBUG
                        Console.WriteLine("Trying to find complete plan for actions:");
                        Console.WriteLine(string.Join(", ", CurrentPlan));
#endif
                        CallClassicalPlanner(currentDirectory);
                        if (File.Exists(Path.Combine(currentDirectory, PLAN_FILE_NAME)))
                        {
                            List<Subplan> allActions = ProcessClassicalPlan(currentDirectory, 0,
                                out var _);
                            newCurrentPlan = CreateNewCurrentPlan(allActions);
                            return true;
                        }
                        else
                        {
                            newCurrentPlan = null;
                            return false;
                        }
                    }
                default:
                    throw new NotSupportedException();
            }
        }

        private bool IsCurrentPlanApplicableInInitialState()
        {
            if (CurrentPlan.Count == 0)
            {
                return true;
            }

            var currentTimeline = CurrentTimeline;
            CurrentTimeline = new();
            bool applicable = base.IsApplicableToCurrentState(CurrentPlan[0].Subplan, out _, out _,
                0, out _, out _);
            CurrentTimeline = currentTimeline;
            return applicable;
        }

        protected override bool RulePreconditionsSatisfied(Subplan subplan, RuleInstance ruleInstance, 
            int timelineIndex,
            List<Subplan> groundedSubtasks, out List<Term> unsatisfiedPosPreconditions,
            out List<Term> unsatisfiedNegPreconditions, out List<Subplan> actionsToInsert,
            out List<Action> correspondingActions)
        {
            actionsToInsert = new();
            unsatisfiedNegPreconditions = new();
            unsatisfiedPosPreconditions = new();
            //return true;
            switch (TASK_INSERTION_MODE)
            {
                case TaskInsertionMode.InsertAllAtOnce:
                    if (base.RulePreconditionsSatisfied(subplan, ruleInstance, timelineIndex,
                       groundedSubtasks,
                       out unsatisfiedPosPreconditions, out unsatisfiedNegPreconditions,
                       out actionsToInsert, out correspondingActions)
                        || PreconditionsCanBeSatisfiedByClassicalPlan(unsatisfiedPosPreconditions,
                            unsatisfiedNegPreconditions))
                    {
                        CurrentPlan[ruleInstance.FirstIndexInCurrentPlan].
                        PosPreconditionsInheritedFromRules.AddRange(
                        ruleInstance.PosPreConditions.Select(x => x.Item2));
                        CurrentPlan[ruleInstance.FirstIndexInCurrentPlan].
                            NegPreconditionsInheritedFromRules.AddRange(
                            ruleInstance.NegPreConditions.Select(x => x.Item2));
                        actionsToInsert = new();
                        unsatisfiedNegPreconditions = new();
                        unsatisfiedPosPreconditions = new();
                        correspondingActions = new List<Action>();
                        return true; // will be checked at the end
                    }
                    else
                    {
                        return false;
                    }
                case TaskInsertionMode.InsertOnTheFly:
                    if (base.RulePreconditionsSatisfied(subplan, ruleInstance, timelineIndex, 
                        groundedSubtasks,
                        out unsatisfiedPosPreconditions, out unsatisfiedNegPreconditions,
                        out actionsToInsert, out correspondingActions))
                    {
                        actionsToInsert = new();
                        unsatisfiedPosPreconditions = new();
                        unsatisfiedNegPreconditions = new();
                        correspondingActions = new();
                        return true;
                    }
                    else // rule preconditions could be satisfied by action insertion
                    {
                        if (PreconditionsCanBeSatisfiedByClassicalPlan(unsatisfiedPosPreconditions,
                            unsatisfiedNegPreconditions))
                        {
                            List<Term> posPreconditions = ruleInstance.PosPreConditions.Select
                                (x => x.Item2).ToList();
                            List<Term> negPreconditions = ruleInstance.NegPreConditions.
                                Select(x => x.Item2).ToList();
                            AddUnsupportedInnerPreconditionsToPreconditions(ruleInstance,
                                posPreconditions, negPreconditions);
                            if (FindActionSequenceUsingClassicalPlanner(
                                posPreconditions,
                                negPreconditions,
                                out actionsToInsert, out correspondingActions,
                                timelineIndex, ruleInstance.FirstIndexInCurrentPlan))
                            {
                                unsatisfiedNegPreconditions.Clear();
                                unsatisfiedPosPreconditions.Clear();
                                return true;
                            }
                            else
                            {
                                return false;
                            }
                        }
                        else
                        {
                            return false;
                        }
                    }
                default: 
                    throw new NotSupportedException();
            }
        }

        private void AddUnsupportedInnerPreconditionsToPreconditions(RuleInstance ruleInstance,
            List<Term> unsatisfiedPosPreconditions, List<Term> unsatisfiedNegPreconditions)
        {
            HashSet<Term> posEffects = new();
            HashSet<Term> negEffects = new();

            HashSet<Term> unsatisfiedPosPreconditionsSet = new();
            
            HashSet<Term> unsatisfiedNegPreconditionsSet = new();

            Debug.Assert(ruleInstance.LastIndexInCurrentPlan == CurrentPlan.Count - 1);

            for (int i = ruleInstance.FirstIndexInCurrentPlan; i <= ruleInstance.LastIndexInCurrentPlan;
                i++)
            {
                List<Term> posPreconditionsOfAction = InstantiateConditionsByActionInstance(
                    CurrentPlan[i].Action.ActionType.PosPreConditions,
                    CurrentPlan[i].Action.ActionInstance);
                List<Term> negPreconditionsOfAction = InstantiateConditionsByActionInstance(
                    CurrentPlan[i].Action.ActionType.NegPreConditions,
                    CurrentPlan[i].Action.ActionInstance);

                foreach (var precond in posPreconditionsOfAction)
                {
                    if (!posEffects.Contains(precond))
                    {
                        unsatisfiedPosPreconditionsSet.Add(precond);
                    }
                }
                foreach (var precond in negPreconditionsOfAction)
                {
                    if (!negEffects.Contains(precond))
                    {
                        unsatisfiedNegPreconditionsSet.Add(precond);
                    }
                }

                List<Term> posEffectsOfAction = InstantiateConditionsByActionInstance(
                    CurrentPlan[i].Action.ActionType.PosPostConditions,
                    CurrentPlan[i].Action.ActionInstance);
                List<Term> negEffectsOfAction = InstantiateConditionsByActionInstance(
                    CurrentPlan[i].Action.ActionType.NegPostConditions,
                    CurrentPlan[i].Action.ActionInstance);

                posEffects.UnionWith(posEffectsOfAction);
                negEffects.UnionWith(negEffectsOfAction);
            }
            unsatisfiedPosPreconditions.AddRange(unsatisfiedPosPreconditionsSet);
            unsatisfiedNegPreconditions.AddRange(unsatisfiedNegPreconditionsSet);
        }

        private List<Term> InstantiateConditionsByActionInstance(
            List<Tuple<string, List<int>>> conditions, Constant[] actionInstance)
        {
            return CreateConditions(actionInstance, conditions, AllConstants);
        }

        protected override Slot Propagate(Slot lastSlot, List<Slot> timeline)
        {
            switch (TASK_INSERTION_MODE)
            {
                case TaskInsertionMode.InsertAllAtOnce:
                    return new();
                case TaskInsertionMode.InsertOnTheFly:
                    return base.Propagate(lastSlot, timeline);
                default:
                    throw new NotSupportedException();
            }    
            
        }

       
        private List<ActionSubplan> CreateNewCurrentPlan(List<Subplan> allActions)
        {
            int indexInCurrentPlan = 0;
            List<ActionSubplan> newCurrentPlan = new();
            for (int indexInNewPlan = 0; indexInNewPlan < allActions.Count; indexInNewPlan++)
            {
                var actionTerm = allActions[indexInNewPlan].Timeline[0].a;
                var actionType = InputReader.FindActionType(AllActionTypes, actionTerm.Name, actionTerm.Variables.Length);
                if (actionType != null)
                {
                    newCurrentPlan.Add(new ActionSubplan(allActions[indexInNewPlan], false, 
                        new Action(actionType, actionTerm.Variables)));
                }
                else
                {
                    newCurrentPlan.Add(CurrentPlan[indexInCurrentPlan++]);
                }
            }
            return newCurrentPlan;
        }

        private List<NewGroundAction> CreateNewActions(out List<Term> newPredicates)
        {
            newPredicates = new();
            List<NewGroundAction> newActions = new();
            foreach (var action in CurrentPlan)
            {
                ActionType originalActionType = InputReader.FindActionType(AllActionTypes, action.Subplan.Timeline[0].a.Name, action.Subplan.Timeline[0].a.Variables.Length);

                Term newPredicate = new($"{TIHTN_ACTION_EFFECT_NAME}_{newPredicates.Count + 1}", Array.Empty<Constant>());
                newPredicates.Add(newPredicate);

                List<Term> posPreconditions = new();
                posPreconditions.AddRange(action.Subplan.Timeline[0].PosPreConditions);
                posPreconditions.AddRange(action.PosPreconditionsInheritedFromRules);

                List<Term> negPreconditions = new();
                negPreconditions.AddRange(action.Subplan.Timeline[0].NegPreConditions);
                negPreconditions.AddRange(action.NegPreconditionsInheritedFromRules);

                List<Term> posPostconditions = new();
                posPostconditions.AddRange(action.Subplan.Timeline[0].PosPostConditions);
                posPostconditions.Add(newPredicate);

                List<Term> negPostconditions = new();
                negPostconditions.AddRange(action.Subplan.Timeline[0].NegPostConditions);

                if (newPredicates.Count > 1)
                {
                    posPreconditions.Add(newPredicates[^2]);
                    negPostconditions.Add(newPredicates[^2]);
                }
                
                NewGroundAction newAction = new(action.Subplan.ActionString(0).Replace("(", "_").Replace(")", "_").Replace(", ", "_") +
                    TIHTN_ACTION_NAME_SUFFIX + $"_{newPredicates.Count}",
                    posPreconditions, negPreconditions, posPostconditions,
                    negPostconditions);

                newActions.Add(newAction);
            }
            return newActions;
        }

        private void DefinePDDLDomain(List<Term> newPredicates = null, IEnumerable<NewGroundAction> newActions = null, string directory = null)
        {
            if (directory == null)
            {
                directory = workingDirectory;
            }
            using (StreamWriter sw = new(Path.Combine(directory, DOMAIN_FILE_NAME)))
            {
                sw.WriteLine($"(define (domain {DOMAIN_NAME})");
                sw.WriteLine("  (:requirements :strips)");
                sw.WriteLine();
                sw.WriteLine("(:predicates ");
                foreach (var predicate in allPredicates)
                {
                    sw.WriteLine($"({predicate.Name} {string.Join(" ", predicate.Variables.Select(x => x.Name).ToArray())})");
                    sw.WriteLine();
                }
                if (newActions != null)
                {
                    foreach (var predicate in newPredicates)
                    {
                        sw.WriteLine($"({predicate.Name} {string.Join(" ", predicate.Variables.Select(x => x.Name).ToArray())})");
                        sw.WriteLine();
                    }
                }
                foreach (var constant in AllConstantTypes)
                {
                    sw.WriteLine($"({constant.Name} ?{constant.Name})");
                    sw.WriteLine();
                }
                sw.WriteLine(")");
                foreach (var action in actionsOutsideHierarchy)
                {
                    sw.WriteLine($"(:action {action.ActionTerm.Name}");
                    sw.WriteLine($"  :parameters ({string.Join(' ', action.ActionTerm.Variables.Select(x => x.Name).ToArray())})");
                    sw.Write("  :precondition (and ");
                    foreach (var param in action.ActionTerm.Variables)
                    {
                        sw.Write($"({param.Type.Name} {param.Name}) ");
                    }
                    foreach (var precondition in action.PosPreConditions)
                    {
                        if (precondition.Item1.Contains('!'))
                        {
                            sw.WriteLine($"({string.Join(' ', precondition.Item1.Split('!'))})");
                        }
                        else
                        {
                            sw.Write($"({precondition.Item1} {string.Join(' ', precondition.Item2
                                .Select(
                                x => action.ActionTerm.Variables[x].Name).ToArray())}) ");
                        }
                        
                    }
                    foreach (var  precondition in action.NegPreConditions)
                    {
                        if (precondition.Item1.Contains('!'))
                        {
                            sw.WriteLine($"(not ({string.Join(' ', precondition.Item1.Split('!'))}))");
                        }
                        else
                        {
                            sw.Write($"(not ({precondition.Item1} {string.Join(' ', precondition.Item2.Select(
                            x => action.ActionTerm.Variables[x].Name).ToArray())})) ");
                        }
                    }
                    sw.WriteLine(")");

                    sw.Write("  :effect (and ");
                    foreach (var effect in action.PosPostConditions)
                    {
                        sw.Write($"({effect.Item1} {string.Join(' ', effect.Item2.Select(
                            x => action.ActionTerm.Variables[x].Name).ToArray())}) ");
                    }
                    foreach (var effect in action.NegPostConditions)
                    {
                        sw.Write($"(not ({effect.Item1} {string.Join(' ', effect.Item2.Select(
                            x => action.ActionTerm.Variables[x].Name).ToArray())})) ");
                    }
                    sw.WriteLine(")");
                    sw.WriteLine(")");
                    sw.WriteLine();
                }
                if (newActions != null)
                {
                    foreach (var action in newActions)
                    {
                        sw.WriteLine($"(:action {action.Name}");
                        sw.WriteLine($"  :parameters ()");
                        sw.Write("  :precondition (and ");
                        
                        foreach (var precondition in action.PosPreconditions)
                        {
                            sw.Write($"({precondition.Name} {string.Join(' ', precondition.Variables.Select(
                                x => x.Name).ToArray())}) ");
                        }
                        foreach (var precondition in action.NegPreconditions)
                        {
                            sw.Write($"(not({precondition.Name} {string.Join(' ', precondition.Variables.Select(
                                x => x.Name).ToArray())})) ");
                        }
                        sw.WriteLine(")");

                        sw.Write("  :effect (and ");
                        foreach (var effect in action.PosPostconditions)
                        {
                            sw.Write($"({effect.Name} {string.Join(' ', effect.Variables.Select(
                                x => x.Name).ToArray())}) ");
                        }
                        foreach (var effect in action.NegPostconditions)
                        {
                            sw.Write($"(not ({effect.Name} {string.Join(' ', effect.Variables.Select(
                                x => x.Name).ToArray())})) ");
                        }
                        sw.WriteLine(")");
                        sw.WriteLine(")");
                        sw.WriteLine();
                    }
                }
                sw.WriteLine(')');
            }
        }

        class NewGroundAction
        {
            public NewGroundAction(string name, List<Term> posPreconditions, List<Term> negPreconditions, 
                List<Term> posPostconditions, List<Term> negPostconditions)
            {
                Name = name;
                PosPreconditions = posPreconditions;
                NegPreconditions = negPreconditions;
                PosPostconditions = posPostconditions;
                NegPostconditions = negPostconditions;
                Constants = FindUsedConstants();
            }

            private List<Constant> FindUsedConstants()
            {
                HashSet<Constant> usedConstants = new();
                usedConstants.UnionWith(PosPreconditions.Union(NegPreconditions).Union(PosPostconditions).Union(NegPostconditions).
                    SelectMany(x => x.Variables));
                return usedConstants.ToList();
            }

            internal string Name { get; private set; }
            internal List<Term> PosPreconditions { get; private set; }
            internal List<Term> NegPreconditions { get; private set; }
            internal List<Term> PosPostconditions { get; private set; }
            internal List<Term> NegPostconditions { get; private set; }
            internal List<Constant> Constants { get; private set; }

        }

        internal enum TaskInsertionMode
        {
            InsertOnTheFly, InsertAllAtOnce
        }
    }
}
