using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Threading;
using PlanRecognitionNETF;

namespace PlanRecognitionExtension
{
    internal class PlanRecognizerExtended : PlanRecognisor
    {
        public bool RecognizePlanWithEarleyPruning(List<Term> plan, List<Action> planPrefix, List<TaskType> allTaskTypes,
            List<ActionType> allActionTypes, List<Term> initState, List<Constant> allConstants, List<ConstantType> allConstantTypes,
            List<Rule> emptyRules, List<Rule> allRules, out Rule finalRule, out Subplan finalSubtask, out List<int> addedActionsByIteration,
            CancellationToken cancellationToken = default)
        {
            List<Rule> rulesExpandedByAllPossibleSubtaskOrderings = ExpandExplicitSubtaskOrdering(allRules);
            SuffixPruner pruner = new EarleyParser();
            pruner.ComputeSupports();
            addedActionsByIteration = new List<int>();


            CreateConstantTypeInstances(allConstants, allConstantTypes);
            int size = plan.Count();
            List<Slot> timeline = CreateEmptyTimeline(plan.Count); // Creates empty timeline of slots for empty subtask creation.
            List<Subplan> subplans = new List<Subplan>();
            List<Subplan> newTasks = new List<Subplan>();
            int level = size;
            bool start = true;
            int i = 0;
            List<Subplan> actionPlans = new List<Subplan>();
            List<Subplan> subplansNew = new List<Subplan>();
            Slot firstMegaslot = null;
            int counterBadMerging = 0;
            int counterNotNew = 0;
            int counterNotValid = 0;
            int iteration = 0;
            Slot prevSlot = null;
            List<Tuple<List<int>, Term, bool>> betweenConditions = new List<Tuple<List<int>, Term, bool>>();
            foreach (Term a in plan)
            {
                Subplan t = CreateTaskFromAction(a, allTaskTypes, allActionTypes, i, size, prevSlot, allConstants);
                if (t == null)
                {
                    finalRule = null;
                    finalSubtask = null;
                    return false;
                }
                newTasks.Add(t);
                i++;
                actionPlans.Add(t);
                t.Iteration = -1; //As these are basic actions we must give them low iteration. So that when we create tasks on iteration 0 it will work.
                if (i == 1)
                {
                    actionPlans[0].GetSlot(0).PosPreConditions = UnifyConditions(actionPlans[0].GetSlot(0).PosPreConditions, initState); // We assume init state has only positive conditions. If it has negative we can simply ignore them as negative just means not in the list of positive.
                    List<Term> c1 = RemoveConditions(actionPlans[0].GetSlot(0).PosPreConditions, actionPlans[0].GetSlot(0).NegPostConditions);
                    actionPlans[0].GetSlot(0).PosPostConditions = UnifyConditions(actionPlans[0].GetSlot(0).PosPostConditions, c1);
                    prevSlot = actionPlans[0].GetSlot(0);
                }
                else
                {
                    prevSlot = t.GetSlot(0);
                }

            }
            subplans.AddRange(newTasks); // to add the basic newtasks from the plan.  
            string name = "FakeSubplanForEmptySubtasks";
            Constant[] constants = new Constant[1];
            Subplan prefixTimeline = MergePlans(newTasks, new Term(name, constants), null, null);
            Propagate(ref prefixTimeline.Timeline);
            newTasks.AddRange(CreateEmptyTasks(emptyRules, prefixTimeline.Timeline, allConstants, false, -1,allConstantTypes));

            HashSet<Tuple<int, Action>> usedActionsByIteration = new HashSet<Tuple<int, Action>>();
            Stopwatch stopWatch = Stopwatch.StartNew();

            bool skipLevel = false;
            List<Slot> megaslotList = new List<Slot>();

            

            while (FullSubplan(plan, subplans, level) == null) 
            {
                Console.WriteLine("Level: " + level);

                if (!skipLevel)
                {
                    while (newTasks != null && newTasks.Any())
                    {
                        if (cancellationToken.IsCancellationRequested)
                        {
                            finalRule = null;
                            finalSubtask = null;
                            addedActionsByIteration = null;
                            return false;
                        }


                        newTasks = newTasks.Distinct().ToList();
                        List<Rule> applicableRules = GetApplicableRules(plan, newTasks, iteration - 1);


                        applicableRules = applicableRules.Distinct().ToList();
                        applicableRules = applicableRules.Except(emptyRules).ToList(); //We have already created basic empty rules. We dont want to create them again.
                        newTasks = new List<Subplan>();
                        foreach (Rule rule in applicableRules)
                        {
                            List<RuleInstance> ruleInstances;
                           
                            ruleInstances = rule.GetRuleInstances(level + 1, allConstants, iteration - 1);
                            foreach (RuleInstance ruleInstance in ruleInstances)
                            {
                                if (cancellationToken.IsCancellationRequested)
                                {
                                    finalRule = null;
                                    finalSubtask = null;
                                    addedActionsByIteration = null;
                                    return false;
                                }
                                List<Subplan> subtasks = new List<Subplan>();
                                Term mainTaskName = ruleInstance.MainTask.TaskInstance;
                                subtasks = ruleInstance.Subtasks;
                                Subplan newSubtask = MergePlans(subtasks, mainTaskName, rule.MainTaskType, prefixTimeline.Timeline);
                                if (newSubtask != null)
                                {
                                    newSubtask.Iteration = iteration;
                                    List<Slot> newTimeline = new List<Slot>();
                                    List<Subplan> allnewtasks = new List<Subplan>(subplans);
                                    allnewtasks.AddRange(newTasks);
                                    bool valid = true;
                                    if (ApplyPre(newSubtask.Timeline, ruleInstance.PosPreConditions, ruleInstance.NegPreConditions, (int)newSubtask.StartIndex, prefixTimeline.Timeline.Count()))
                                    {
                                        ApplyPost(newSubtask.Timeline, ruleInstance.PosPostConditions, ruleInstance.NegPostConditions);
                                        valid = ApplyBetween(newSubtask.Timeline, ruleInstance.PosBetweenConditions, ruleInstance.NegBetweenConditions, (int)Math.Ceiling(newSubtask.StartIndex), prefixTimeline.Timeline.Count);
                                        if (newSubtask.EndIndex >= prefixTimeline.Timeline.Count() && valid)
                                        {
                                            valid = MegaslotPropagate(ref newSubtask.Timeline, prefixTimeline.Timeline.Count(), (int)Math.Ceiling(newSubtask.StartIndex));
                                        }
                                        if (valid && CheckValidity(newSubtask.Timeline)) //validity should be easier than check newness so it goes first. 
                                        {
                                            if (CheckNewness(newSubtask, allnewtasks))
                                            {
                                                //The new subtask is valid. So it can be added to the newTasks.
                                                newTasks.Add(newSubtask);
                                                newSubtask.AddToHistory(ruleInstance);
                                                newSubtask.CreateUsedActions(subtasks);
                                                if (IsGoalTask(newSubtask, plan))
                                                {
                                                    finalRule = rule;
                                                    finalSubtask = newSubtask;
                                                    return true;
                                                }
                                            }
                                            else
                                            {
                                                counterNotNew++;
                                            }

                                        }
                                    }
                                    else
                                    {
                                        counterNotValid++;
                                    }
                                }
                                else
                                {
                                    counterBadMerging++;
                                }
                            }
                        }
                        subplans.AddRange(newTasks);
                        iteration++;
                    }
                    
                    
                }


                stopWatch.Stop();

                Console.WriteLine("\tTime: " + stopWatch.ElapsedMilliseconds + " ms");

                if (firstMegaslot == null)
                {
                    firstMegaslot = CreateMegaSlotFirst(actionPlans);
                } // other slots will be created inside CreateNewActionsPruned
                megaslotList = new List<Slot>
                        {
                            firstMegaslot
                        };
                stopWatch.Restart();
                subplansNew = CreateNewActionsPruned(pruner, megaslotList, allTaskTypes, allActionTypes, level, allConstants, allConstantTypes, iteration,
                    planPrefix, rulesExpandedByAllPossibleSubtaskOrderings, usedActionsByIteration, cancellationToken);

                if (cancellationToken.IsCancellationRequested)
                {
                    finalRule = null;
                    finalSubtask = null;
                    addedActionsByIteration = null;
                    return false;
                }
                
                stopWatch.Stop();

                Console.WriteLine("\tPruning time: " + stopWatch.ElapsedMilliseconds / 1000f + " s");

                stopWatch.Restart();

                if (subplansNew != null)
                {
                    skipLevel = false;
                    
                    subplansNew.AddRange(CreateEmptyTasks(emptyRules, megaslotList[megaslotList.Count - 1], allConstants, true, iteration,allConstantTypes));

                   

                    newTasks = subplansNew;
                    addedActionsByIteration.Add(subplansNew.Count);
                    Console.WriteLine("\tAdded actions: " + subplansNew.Count);
                }
                else
                {
                    addedActionsByIteration.Add(0);
                    Console.WriteLine("\tNo actions found for current suffix length.");
                    skipLevel = true;
                }
                level = level + 1; 
                iteration++;
            }

            if (FullSubplan(plan, subplans, level) == null)
            {
                finalRule = null;
                finalSubtask = null;
                return false;
            }

            finalRule = null;
            finalSubtask = null;
            return true;

        }

        protected List<Rule> ExpandExplicitSubtaskOrdering(List<Rule> allRules)
        {
            List<Rule> result = new List<Rule>();
            foreach (Rule rule in allRules)
            {
                List<List<int>> allSubtaskOrderings = rule.GetExplicitSubtaskOrdering();
                if (allSubtaskOrderings != null) // null for empty rules - not needed in Earley pruner
                {
                    for (int o = 0; o < allSubtaskOrderings.Count; o++)
                    {
                        List<int> ordering = allSubtaskOrderings[o];
                        TaskType[] taskTypeArray = new TaskType[ordering.Count];
                        List<int>[] arrayOfReferenceLists = new List<int>[ordering.Count];
                        bool changed = false;
                        for (int i = 0; i < ordering.Count; i++)
                        {
                            if (taskTypeArray[i] != rule.TaskTypeArray[ordering[i]])
                            {
                                changed = true;
                            }
                            taskTypeArray[i] = rule.TaskTypeArray[ordering[i]];
                            arrayOfReferenceLists[i] = rule.ArrayOfReferenceLists[ordering[i]];
                        }
                        if (changed)
                        {
                            Rule newRule = new Rule
                            {
                                Name = o > 0 ? rule.Name + "_" + o : rule.Name,
                                MainTaskType = rule.MainTaskType,
                                TaskTypeArray = taskTypeArray,
                                ArrayOfReferenceLists = arrayOfReferenceLists,
                                MainTaskReferences = rule.MainTaskReferences,
                                AllVars = rule.AllVars,
                                AllVarsTypes = rule.AllVarsTypes,
                                posPreConditions = rule.posPreConditions,
                                negPreConditions = rule.negPreConditions,
                                posPostConditions = rule.posPostConditions,
                                negPostConditions = rule.negPostConditions,
                                posBetweenConditions = rule.posBetweenConditions,
                                negBetweenConditions = rule.negBetweenConditions
                            };
                            result.Add(newRule);
                        }
                        else
                        {
                            result.Add(rule);
                        }
                    }
                }
                else
                {
                    result.Add(rule); // default ordering
                }
            }
            return result;
        }

        private List<Subplan> CreateEmptyTasks(List<Rule> emptyRules, Slot slot, List<Constant> allConstants, bool isMegaslot, int iteration, List<ConstantType> AllConstantTypes) 
        {
            List<Subplan> validTasks = new List<Subplan>();
            foreach (Rule r in emptyRules)
            {
                validTasks.AddRange(CreateEmptySubtaskFromSlot(r, slot, allConstants, 0, 1, isMegaslot, iteration,AllConstantTypes));
            }
            return validTasks;
        }

        private List<List<Constant>> GetConstants(Constant[] variables, List<Constant> allConstants, List<ConstantType> allConstantTypes,
            List<Constant> partialConst, int level, ref List<List<Constant>> solutions,
            Dictionary<int, Constant> variablesToSkip /* extended by partially instantiated actions */)
        {

            if (level == variables.Length)
            {
                solutions.Add(partialConst);
                partialConst = new List<Constant>();
                return solutions;
            }
            else
            {
                if (variablesToSkip.TryGetValue(level, out Constant constant))
                {
                    List<Constant> newPartialConst = new List<Constant>(partialConst);
                    newPartialConst.Add(constant);
                    solutions = GetConstants(variables, allConstants, allConstantTypes, newPartialConst, level + 1, ref solutions, variablesToSkip);
                }
                else
                {
                    ConstantType desiredType = variables[level].Type;
                    foreach (ConstantType ct in desiredType.DescendantTypes)
                    {
                        foreach (Constant c in ct.Instances) //This goes through less constants then before. Before it went through all of them, now it goes through less. 
                        {
                            List<Constant> newPartialConst = new List<Constant>(partialConst);
                            newPartialConst.Add(c);
                            solutions = GetConstants(variables, allConstants, allConstantTypes, newPartialConst, level + 1, ref solutions, variablesToSkip);
                        }
                    }
                }

                return solutions;
            }
        }

        private List<Subplan> CreateTasksFromPartiallyInstantiatedAction(Action action, List<TaskType> allTaskTypes, List<ActionType> allActions,
            int timelinePosition, List<Constant> allConstants, List<ConstantType> allConstantTypes, int iteration, out List<Action> instantiatedActions)
        {
            IEnumerable<Tuple<Subplan, Action>> result = GenerateTasksFromPartiallyInstantiatedAction(action,allTaskTypes,allActions,timelinePosition,allConstants,allConstantTypes,iteration);
            instantiatedActions = result.Select( x => x.Item2).ToList();
            return result.Select(x => x.Item1).ToList();
        }

        public IEnumerable<Tuple<Subplan, Action>> GenerateTasksFromPartiallyInstantiatedAction(Action action, List<TaskType> allTaskTypes, List<ActionType> allActions,
            int timelinePosition, List<Constant> allConstants, List<ConstantType> allConstantTypes, int iteration, bool usedActionFromPlan = true)
        {
           
            TaskType taskType = FindTaskType(action.ActionType.ActionTerm, allTaskTypes);
            String actionName = action.ActionType.ActionTerm.Name;
            List<List<Constant>> sols = new List<List<Constant>>();

            Dictionary<int, Constant> variablesToSkip = new Dictionary<int, Constant>();
            for (int i = 0; i < action.ActionInstance.Length; i++)
            {
                if (action.ActionInstance[i] != null && action.ActionInstance[i].Name != null && action.ActionInstance[i].Name.Length > 0)
                {
                    variablesToSkip.Add(i, action.ActionInstance[i]);
                }
            }

            for (int i = 0; i < action.ActionInstance.Length; i++)
            {
                if (action.ActionInstance[i] == null || action.ActionInstance[i].Type == null)
                {
                    action.ActionInstance[i] = new Constant(null, action.ActionType.ActionTerm.Variables[i].Type);
                }
            }

            List<List<Constant>> sol = GetConstants(action.ActionInstance, allConstants, allConstantTypes, new List<Constant>(), 0, ref sols,
                variablesToSkip); //Returns al possible fillings of this action with constants. 

            foreach (List<Constant> consts in sol)
            {
                Term term = new Term(actionName, consts.ToArray());
                Subplan t = new Subplan(term, timelinePosition, timelinePosition, taskType);
                Slot s = CreateConditionsSlot(t, allActions, allConstants);
                t.SetSlot(0, s);
                t.Iteration = iteration;
                if (usedActionFromPlan)
                {
                    t.usedActions = new bool[timelinePosition + 1];
                    t.usedActions[timelinePosition] = true;
                }
                else
                {
                    t.usedActions = Array.Empty<bool>();
                }
                yield return new Tuple<Subplan, Action>(t, new Action(action.ActionType, consts.ToArray()));
            }
        }

        private List<Subplan> CreateNewActionsPruned(SuffixPruner pruner, List<Slot> megaslotList, List<TaskType> allTaskTypes, List<ActionType> allActions,
            int level, List<Constant> allConstants, List<ConstantType> allConstantTypes, int iteration, List<Action> planPrefix, List<Rule> allRules,
            HashSet<Tuple<int, Action>> alreadyUsedActions, CancellationToken cancellationToken)
        {
            List<List<Action>> prunedDomains = pruner.GetPrunedPlanSuffix(planPrefix, level - planPrefix.Count, allActions, allRules, allTaskTypes, cancellationToken);

            List<Subplan> newsubplans = new List<Subplan>();
            List<Subplan> newSubplansOnLastLevel = new List<Subplan>();
            if (prunedDomains == null)
            {
                return null;
            }
            else 
            {
                for (int i = planPrefix.Count; i < prunedDomains.Count; i++)
                {
                    if (megaslotList.Count < i - planPrefix.Count + 1) // new megaslot based on actions added on previous level must be created
                    {
                        Slot nextMegaslot = CreateNextMegaSlot(megaslotList[i - planPrefix.Count - 1], newSubplansOnLastLevel);
                        megaslotList.Add(nextMegaslot);
                    }
                    Slot slot = megaslotList[i - planPrefix.Count];
                    newSubplansOnLastLevel = new List<Subplan>();
                    foreach (Action action in prunedDomains[i])
                    {

                        String name = action.ActionType.ActionTerm.Name;
                        Constant[] vars = new Constant[action.ActionType.ActionTerm.Variables.Length];
                        int validPreconditions = 0;

                        List<Subplan> plans;
                        List<Action> instantiatedActions;
                        if (action.ActionType.PosPreConditions == null || !action.ActionType.PosPreConditions.Any())
                        {
                            plans = CreateTasksFromPartiallyInstantiatedAction(action, allTaskTypes, allActions, i, allConstants,
                                allConstantTypes, iteration, out instantiatedActions);

                            for (int j = 0; j < instantiatedActions.Count; j++)
                            {
                                Action a = instantiatedActions[j];
                                var indexActionTuple = new Tuple<int, Action>(i, a);
                                if (!alreadyUsedActions.Contains(indexActionTuple))
                                {
                                    newsubplans.Add(plans[j]);
                                    alreadyUsedActions.Add(indexActionTuple);
                                }
                                newSubplansOnLastLevel.Add(plans[j]);
                            }
                        }
                        else
                        {
                            foreach (Term condition in slot.PosPreConditions)
                            {
                                foreach (Tuple<String, List<int>> preConditionType in action.ActionType.PosPreConditions)
                                {
                                    if (preConditionType.Item1.Equals(condition.Name) && (preConditionType.Item2.Count == condition.Variables.Length))
                                    {
                                        validPreconditions++;
                                        if (validPreconditions == action.ActionType.PosPreConditions.Count)
                                        {
                                            plans = CreateTasksFromPartiallyInstantiatedAction(action, allTaskTypes, allActions, i /*i+1*/, allConstants, allConstantTypes,
                                                iteration, out instantiatedActions);

                                            for (int j = 0; j < instantiatedActions.Count; j++)
                                            {
                                                Action a = instantiatedActions[j];
                                                var indexActionTuple = new Tuple<int, Action>(i, a);
                                                if (!alreadyUsedActions.Contains(indexActionTuple)) 
                                                {
                                                    newsubplans.Add(plans[j]);
                                                    alreadyUsedActions.Add(indexActionTuple);
                                                }
                                                newSubplansOnLastLevel.Add(plans[j]);
                                            }
                                        }
                                    }
                                }
                            }

                        }

                    }
                }
                return newsubplans.Distinct().ToList();
            }
        }

        internal static void AddTaskToActionRules(List<ActionType> allActionTypes, List<Rule> allRules, List<TaskType> allTaskTypes)
        {
            foreach (var actionType in allActionTypes)
            {
                ActionTaskType actionTaskType = new ActionTaskType(actionType.ActionTerm.Name, actionType.ActionTerm.Variables.Length, actionType);
                actionTaskType.TaskTerm = actionType.ActionTerm;
                TaskType correspondingTaskType = PlanRecognisor.FindTaskType(actionType.ActionTerm, allTaskTypes);
                if (correspondingTaskType != null)
                {
                    correspondingTaskType.TaskTerm = actionType.ActionTerm;
                    List<int>[] arrayOfReferenceLists = new List<int>[1];
                    arrayOfReferenceLists[0] = Enumerable.Range(0, correspondingTaskType.NumOfVariables).ToList();
                    Rule rule = new Rule()
                    {
                        MainTaskType = correspondingTaskType,
                        TaskTypeArray = new TaskType[] { actionTaskType },
                        ArrayOfReferenceLists = arrayOfReferenceLists,
                        MainTaskReferences = arrayOfReferenceLists[0]
                    };
                    allRules.Add(rule);
                }
            }
        }
    }
}
