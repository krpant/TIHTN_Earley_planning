using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Threading;

namespace PlanRecognitionNETF
{
    class PlanRecognisor
    {

        /// <summary>
        /// Tries to recognize a plan from prefix. Three possible outcomes: it will output a valid plan, it will run forever, it will say the plan is invalid if the prefix of the plan is invalid.
        /// </summary>
        /// <param name="plan">The prefix pan</param>
        /// <param name="allTaskTypes"></param>
        /// <param name="allActions"></param>
        /// <param name="initState"></param>
        /// <param name="allConstants"></param>
        /// <param name="allConstantTypes"></param>
        /// <param name="emptyRules"></param>
        /// <param name="finalRule">Output</param>
        /// <param name="finalSubtask">Output</param>
        /// <returns></returns>
        public bool RecognizePlan(List<Term> plan, List<TaskType> allTaskTypes, List<ActionType> allActions, List<Term> initState, 
            List<Constant> allConstants, List<ConstantType> allConstantTypes, List<Rule> emptyRules, out Rule finalRule, out Subplan finalSubtask,
            out List<int> addedActionsByIteration,  CancellationToken cancellationToken = default)
        {
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
            Slot megaslot = null;
            int counterBadMerging = 0;
            int counterNotNew = 0;
            int counterNotValid = 0;
            int iteration = 0;
            Slot prevSlot = null;
            List<Tuple<List<int>, Term, bool>> betweenConditions = new List<Tuple<List<int>, Term, bool>>();
            for (int i1 = 0; i1 < plan.Count; i1++)
            {
                Term a = plan[i1];
                Subplan t = CreateTaskFromAction(a, allTaskTypes, allActions, i, size, prevSlot, allConstants);
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
            Stopwatch stopWatch = Stopwatch.StartNew();
            List<Subplan> addedActionsOnly = new List<Subplan>(); 
            while (FullSubplan(plan, subplans, level) == null) 
            {
                Console.WriteLine("Level: " + level);
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
                        List<RuleInstance> ruleInstances = rule.GetRuleInstances(level + 1, allConstants, iteration - 1);
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
                if (megaslot == null) megaslot = CreateMegaSlotFirst(actionPlans);
                else megaslot = CreateNextMegaSlot(megaslot, addedActionsOnly); 
                
                stopWatch.Stop();

                Console.WriteLine("\tTime: " + stopWatch.ElapsedMilliseconds/1000f + " s");
                stopWatch.Restart();
                addedActionsOnly=new List<Subplan>();
                subplansNew = CreateNewActions(megaslot, allTaskTypes, allActions, level, allConstants, allConstantTypes, iteration, cancellationToken);
                addedActionsOnly.AddRange(subplansNew);
                if (cancellationToken.IsCancellationRequested) 
                {
                    finalRule = null;
                    finalSubtask = null;
                    addedActionsByIteration = null;
                    return false;
                }

                List<Slot> megaslotList = new List<Slot>();
                megaslotList.Add(megaslot);
                subplansNew.AddRange(CreateEmptyTasks(emptyRules, megaslotList, allConstants, true, iteration,allConstantTypes));
                level = level + 1; 
                newTasks = subplansNew;
                addedActionsByIteration.Add(subplansNew.Count);
                Console.WriteLine("\tAdded actions and empty tasks: " + subplansNew.Count); 
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

        /// <summary>
        /// Checks if initial stat contains all positive preconditions and no negative preconditions of this subtasks that start on position 0.
        /// Intitial state only has positive conditions. 
        /// </summary>
        /// <param name="newSubtask"></param>
        /// <param name="initState"></param>
        /// <returns></returns>
        protected bool CheckInitialState(Subplan newSubtask, List<Term> initState)
        {
            foreach (Term c in newSubtask.GetSlot(0).PosPreConditions)
            {
                if (!initState.Contains(c))
                {
                    Console.WriteLine("Task {0}, does nto have precondition {1} in initState", newSubtask, c);
                    return false;
                }
            }
            foreach (Term c2 in newSubtask.GetSlot(0).NegPreConditions)
            {
                if (initState.Contains(c2))
                {
                    Console.WriteLine("Task {0}, has opposite of negative precondition {1} in initState", newSubtask, c2);
                    return false;
                }
            }
            return true;

        }
        /// <summary>
        /// Creates very first megaslot. Propagates effects and precondtions from the last action in the prefixed plan forward. 
        /// Iń megaslot we have as preconditions everything that could be true (not necessarily is true).
        /// </summary>
        /// <param name="actionPlans"></param>
        /// <returns></returns>
        protected Slot CreateMegaSlotFirst(List<Subplan> actionPlans)
        {
            List<Slot> newSlots = new List<Slot>();
            foreach (Subplan act in actionPlans)
            {
                newSlots.Add(act.GetSlot(0)); // we know that each action is only in one slot. 
            }
            newSlots.Add(new Slot()); // final slot the megaslot
            Propagate(ref newSlots);
            return newSlots.Last();
        }

        /// <summary>
        /// Gives constants to instances of the right constant type. 
        /// This cannot be done on constant creation as some constants (the ones with ?) are actually variables. 
        /// </summary>
        /// <param name="allConstants"></param>
        /// <param name="allConstantTypes"></param>
        protected void CreateConstantTypeInstances(List<Constant> allConstants, List<ConstantType> allConstantTypes)
        {
            foreach (Constant c in allConstants)
            {
                c.Type.AddInstance(c);
            }
        }

        /// <summary>
        /// Creates task from action. Slot s2 is the previous slot to this one. 
        /// </summary>
        /// <param name="a"></param>
        /// <param name="allTaskTypes"></param>
        /// <param name="allActions"></param>
        /// <param name="i"></param>
        /// <param name="planSize"></param>
        /// <param name="s2"></param>
        /// <returns></returns>
        protected Subplan CreateTaskFromAction(Term a, List<TaskType> allTaskTypes, List<ActionType> allActions, int i, int planSize, Slot s2, 
            List<Constant> allConstants)
        {
            TaskType t = FindTaskType(a, allTaskTypes);
            Subplan sub = new Subplan(a, i, i, t);
            sub.usedActions = new bool[planSize];
            sub.usedActions[i] = true;
            Slot s = CreateConditionsSlot(sub, allActions, allConstants);
            if (s2 != null)
            {
                List<Term> toRemove = new List<Term>();
                foreach (Term cond in s.PosPreConditions)
                {
                    if (cond.Variables.Contains(null))
                    {
                        if (CheckNullConditions(s2.PosPostConditions, cond))
                        {
                            toRemove.Add(cond);
                            //There exists some other conditon fulfilling this exist condition so I can remove the exist condition. 
                        }
                    }
                    else if (!s2.PosPostConditions.Contains(cond))
                    {
                        if (cond.Name.Contains("=") || cond.Name.Contains("equal"))
                        {
                            if (!cond.CheckEquality(true)) Console.WriteLine("Error: This equality condition {0} is not fulfillled for this action {1}. The prefix of the plan is invalid, therefore the plan is invalid.", cond, sub.TaskInstance);

                        }
                        else
                        {
                            Console.WriteLine("Error: This condition {0} is not fulfillled for this action {1}. The prefix of the plan is invalid, therefore the plan is invalid.", cond, sub.TaskInstance);
                            return null;
                        }
                    }
                }
                s.PosPreConditions = RemoveConditions(s.PosPreConditions, toRemove);
                toRemove = new List<Term>();

                foreach (Term cond in s.NegPreConditions)
                {
                    if (cond.Variables.Contains(null))
                    {
                        if (CheckNullConditions(s2.PosPostConditions, cond))
                        {
                            toRemove.Add(cond);
                            //There exists some other conditon fulfilling this exist condition so I can remove the exist condition. 
                        }
                    }
                    if (s.PosPreConditions.Contains(cond))
                    {
                        //Positive precondtions contain my negative precodntion so its invalid:
                        Console.WriteLine("Error: This negative condition {0} is present as a positive condition for this action {1}. The prefix of the plan is invalid, therefore the plan is invalid.", cond, sub.TaskInstance);
                    }
                    //With negative conditions we must first check do the same check as with positive, but also we must check whether we don't have the same conditon in positive and negative slot.
                    //This for tasks is done with the CheckValidity call.
                }
                RemoveConditions(s.NegPreConditions, toRemove);
                if (!s.IsValid())
                {
                    Console.WriteLine("Error: This slot contains same negative and positive conditions. Therefor the prefix plan is invalid and therofe the plan is invalid. {0}", s);
                    return null;
                }
            }

            List<Slot> timeline = new List<Slot>();
            timeline.Add(s2);
            timeline.Add(s);
            Propagate(ref timeline);
            SelfPropagate(timeline[1]);
            sub.SetSlot(0, timeline[1]);
            t.SetMinTaskLengthIfSmaller(1);
            return sub;
        }

        /// <summary>
        /// Returns true if given task is goal. 
        /// </summary>
        /// <param name="s"></param>
        /// <param name="plan"></param>
        /// <returns></returns>
        protected bool IsGoalTask(Subplan s, List<Term> plan)
        {
            if (s.PlanLength() < 4) return false;
            if (s.Timeline.Count < plan.Count) return false; //Cannot be goal task as it does not even have enough slots for all actions. 

            for (int i = 0; i < plan.Count; i++)
            {
                if (!plan[i].Equals(s.Timeline[i].a)) return false;
            }

            for (int i = plan.Count; i < s.Timeline.Count; i++)
            {
                if (s.Timeline[i].a == null)
                {
                    return false;
                }
            }

            //All actions are in the task and in right order. 
            return true;
        }

        /// <summary>
        /// Creates tasks that have no subtasks. Their boolean number is dependant on which slot satisfies it's conditions-0,5, unless it's on slot 0 then it's 0.
        /// This can be also used to create empty subtasks above a megaslot. 
        /// </summary>
        protected List<Subplan> CreateEmptyTasks(List<Rule> emptyRules, List<Slot> timeline, List<Constant> allConstants, bool isMegaslot, int iteration, List<ConstantType> AllVarsTypes) 
        {
            List<Subplan> validTasks = new List<Subplan>();
            foreach (Rule r in emptyRules)
            {
                for (int i = 0; i < timeline.Count(); i++)
                {
                    validTasks.AddRange(CreateEmptySubtaskFromSlot(r, timeline[i], allConstants, i, timeline.Count, isMegaslot, iteration,AllVarsTypes));
                }
            }
            return validTasks;
        }

        /// <summary>
        /// Creates an empty task above a slot. If the slot is a megaslot it ignores negative preconditions, because even if negative precondition is in the megaslot the task still might be valid. 
        /// </summary>
        /// <param name="r"></param>
        /// <param name="s"></param>
        /// <param name="allConstants"></param>
        /// <param name="i"></param>
        /// <param name="size"></param>
        /// <param name="isMegaSlot"></param>
        /// <returns></returns>
        protected List<Subplan> CreateEmptySubtaskFromSlot(Rule r, Slot s, List<Constant> allConstants, int i, int size, bool isMegaSlot, int iteration, List<ConstantType> AllVarsTypes)
        {
            List<Subplan> validTasks = new List<Subplan>();
            Constant[] emptyConst = new Constant[r.AllVars.Count]; 
            List<Subplan> suitableTasks= new List<Subplan>(); 
            if (r.posPreConditions == null || !r.posPreConditions.Any()) suitableTasks = FillTaskWithNoPreconditions(r, s, emptyConst.ToList(), 0, i, size, new List<Subplan>(), allConstants);
            else
            {
                suitableTasks = FillTaskFromSlot(r, s, emptyConst.ToList(), 0, i, size, new List<Subplan>(),allConstants,AllVarsTypes);
            }

            //Now I must check negative preconditions for these tasks. 
            if (isMegaSlot == false)
            {
                if (suitableTasks != null)
                {
                    foreach (Subplan t in suitableTasks)
                    {
                        if (!t.TaskInstance.Variables.Contains(null))
                        {
                            RuleInstance rI = new RuleInstance(t, null, r, t.TaskInstance.Variables.Select(x => x.Name).ToList(), allConstants);
                            bool valid = CheckNegPreconditions(rI.NegPreConditions.Select(x => x.Item2).ToList(), s);
                            if (valid)
                            {
                                validTasks.Add(t);
                                t.TaskType.SetMinTaskLengthIfSmaller(0);
                                t.Iteration = iteration;
                            }
                        }
                    }
                }
            }
            else validTasks.AddRange(suitableTasks); //It's in a megaslot so I can ignore negative precodnitions. 
            return validTasks;

        }

        /// <summary>
        /// Returns true if slot does not contain any of the negative conditions. 
        /// </summary>
        /// <param name="negConditions"></param>
        /// <param name="s"></param>
        /// <returns></returns>
        protected bool CheckNegPreconditions(List<Term> negConditions, Slot s)
        {
            foreach (Term c in negConditions)
            {
                
                List<Term> conditions = s.PosPreConditions.Where(x => x.Name == c.Name).ToList();
                foreach (Term slotC in conditions)
                {
                    bool same = false;
                    if (slotC.Variables.Count() == c.Variables.Count())
                    {
                        for (int i = 0; i < slotC.Variables.Count(); i++)
                        {
                            if (slotC.Variables[i] == c.Variables[i])
                            {
                                same = true;
                            }
                        }
                        if (same == true) return false; //At least one negative condition is present in this slot. 
                    }
                }
            }
            return true;
        }

        /// <summary>
        /// Returns task created from empty rule r if the conditions fit the task otherwise return null. 
        /// </summary>
        /// <param name="r"></param>
        /// <param name="s"></param>
        /// <returns></returns>
        protected List<Subplan> FillTaskFromSlot(Rule r, Slot s, List<Constant> partialAllVars, int index, int slotNumber, int taskBoolSize, List<Subplan> solution, List<Constant> allConstants, List<ConstantType> AllVarsTypes)
        {
            List<Constant> newPartialVars = new List<Constant>(partialAllVars);
            if (index == r.posPreConditions.Count)
            {

                List<List<Constant>> newAllVars = new List<List<Constant>>();
                if (newPartialVars.Contains(null))
                {
                    newAllVars = r.FillWithAllConstants(newPartialVars, AllVarsTypes, allConstants, new List<List<Constant>>());
                }
                else { newAllVars.Add(newPartialVars); }
                foreach (List<Constant> partialVars in newAllVars)
                {
                    Term term = r.FillMainTaskFromAllVarsReturnTerm(partialVars);
                    Subplan t;
                    t = new Subplan(term, slotNumber - 0.5, slotNumber - 0.5, r.MainTaskType);
                    solution.Add(t);
                }
                return solution;
            }
            Tuple<int, string, List<int>> cond = r.posPreConditions[index];
            List<Term> conditions = s.PosPreConditions.Where(x => x.Name == cond.Item2).ToList(); //conditions of same name in slot.             
            if (conditions == null || !conditions.Any()) return solution; //there is no conditions that could fill my preconditions. I can skip this slot. It cannot fulfill my rule.
            else
            {
                ConstantType DesiredType = r.AllVarsTypes[index];
                foreach (Term c in conditions)
                {
                    bool valid = true;
                    //This conditions might fill my subplan. If so I must fill allvars in this subplan with appropiate string. 
                    for (int i = 0; i < cond.Item3.Count; i++)
                    {                        
                        Constant myConst = c.Variables[i];
                        if (DesiredType.IsAncestorTo(myConst.Type))
                        {
                            if (newPartialVars[cond.Item3[i]] == null) newPartialVars[cond.Item3[i]] = myConst;
                            else if (newPartialVars[cond.Item3[i]] != myConst) return null;
                        }
                        else
                        {
                            valid = false;
                        }
                    }
                    if (valid)
                    {
                        List<Subplan> newTasks = FillTaskFromSlot(r, s, newPartialVars, index + 1, slotNumber, taskBoolSize, solution, allConstants, AllVarsTypes);
                        solution.AddRange(newTasks);
                        solution = solution.Distinct().ToList();
                    }
                    newPartialVars = new List<Constant>(partialAllVars);
                }
                return solution;
            }
        }




        /// <summary>
        /// Returns list of tasks with filled appropiate constants based on type of constant. 
        /// </summary>
        /// <param name="r"></param>
        /// <param name="s"></param>
        /// <param name="partialAllVars"></param>
        /// <param name="index"></param>
        /// <param name="slotNumber"></param>
        /// <param name="taskBoolSize"></param>
        /// <param name="solution"></param>
        protected List<Subplan> FillTaskWithNoPreconditions(Rule r, Slot s, List<Constant> partialAllVars, int index, int slotNumber, int taskBoolSize, List<Subplan> solution, List<Constant> allConstants)
        {
            if (index == partialAllVars.Count())
            {
                Term term = new Term(r.MainTaskType.Name, partialAllVars.ToArray());
                Subplan t;

                
                t = new Subplan(term, slotNumber - 0.5, slotNumber - 0.5, r.MainTaskType);

                solution.Add(t);
                return solution;
            }
            else
            {
                if (partialAllVars[index] != null)
                {
                    //This only happens if the empty rule has real constant as parameter. 
                    List<Subplan> newTasks = FillTaskWithNoPreconditions(r, s, partialAllVars, index++, slotNumber, taskBoolSize, solution, allConstants);
                    solution.AddRange(newTasks);
                    solution = solution.Distinct().ToList();
                }
                else
                {
                    ConstantType desiredType = r.AllVarsTypes[index];
                    List<Constant> fittingConstants = allConstants.Where(x => desiredType.IsAncestorTo(x.Type)).ToList();
                    List<Constant> newPartialVars = new List<Constant>(partialAllVars);
                    foreach (Constant c in fittingConstants)
                    {
                        newPartialVars[index] = c;
                        List<Subplan> newTasks = FillTaskWithNoPreconditions(r, s, newPartialVars, index + 1, slotNumber, taskBoolSize, solution, allConstants);
                        solution.AddRange(newTasks);
                        solution = solution.Distinct().ToList();
                        newPartialVars = new List<Constant>(partialAllVars);
                    }

                }
                return solution;
            }
        }

        /// <summary>
        /// Creates new actions above a megaslot. 
        /// </summary>
        /// <param name="slot"></param>
        /// <param name="allTaskTypes"></param>
        /// <param name="allActions"></param>
        /// <param name="level"></param>
        /// <param name="allConstants"></param>
        /// <param name="allConstantTypes"></param>
        /// <param name="iteration"></param>
        /// <returns></returns>
        protected List<Subplan> CreateNewActions(Slot slot, List<TaskType> allTaskTypes, List<ActionType> allActions, int level, List<Constant> allConstants, 
            List<ConstantType> allConstantTypes, int iteration, CancellationToken cancellationToken)
        {
            List<Subplan> newsubplans = new List<Subplan>();
            foreach (ActionType a in allActions)
            { 
                if (cancellationToken.IsCancellationRequested) 
                {
                    return null;
                }

            String name = a.ActionTerm.Name;
                Constant[] vars = new Constant[a.ActionTerm.Variables.Length];
                int validPreconditions = 0;

                List<Subplan> plans;
                if (a.PosPreConditions == null || !a.PosPreConditions.Any())
                {
                    plans = CreateTasksFromAction(a, allTaskTypes, allActions, level, allConstants, allConstantTypes, iteration, cancellationToken);
                    newsubplans.AddRange(plans);

                }
                else
                {
                    foreach (Term condition in slot.PosPreConditions)
                    {
                        foreach (Tuple<String, List<int>> preConditionType in a.PosPreConditions)
                        {
                            if (preConditionType.Item1.Equals(condition.Name) && (preConditionType.Item2.Count == condition.Variables.Length))
                            {
                                validPreconditions++;
                                if (validPreconditions == a.PosPreConditions.Count)
                                {
                                    plans = CreateTasksFromAction(a, allTaskTypes, allActions, level, allConstants, allConstantTypes, iteration, cancellationToken);
                                    newsubplans.AddRange(plans);
                                }
                            }
                        }
                    }
                }
            }
            return newsubplans.Distinct().ToList();
        }

        /// <summary>
        /// Creates task from actions. 
        /// In plan recognition we have no class action so we must immediately transform any action to task (subplan). That is why the method above this calls this to create a task. 
        /// </summary>
        /// <param name="actionT"></param>
        /// <param name="allTaskTypes"></param>
        /// <param name="allActions"></param>
        /// <param name="timelinePosition"></param>
        /// <param name="allConstants"></param>
        /// <param name="allConstantTypes"></param>
        /// <param name="iteration"></param>
        /// <returns></returns>
        protected List<Subplan> CreateTasksFromAction(ActionType actionT, List<TaskType> allTaskTypes, List<ActionType> allActions, int timelinePosition, List<Constant> allConstants, 
            List<ConstantType> allConstantTypes, int iteration, CancellationToken cancellationToken)
        {
            List<Subplan> subplansNew = new List<Subplan>();
            TaskType taskType = FindTaskType(actionT.ActionTerm, allTaskTypes);
            String actionName = actionT.ActionTerm.Name;
            List<List<Constant>> sols = new List<List<Constant>>();
            List<List<Constant>> sol = GetConstants(actionT, allConstants, allConstantTypes, new List<Constant>(), 0, ref sols, cancellationToken); //Returns al possible fillings of this action with constants. 
            foreach (List<Constant> consts in sol)
            {
                if (cancellationToken.IsCancellationRequested) 
                {
                    return null;
                }

                Term term = new Term(actionName, consts.ToArray());
                Subplan t = new Subplan(term, timelinePosition, timelinePosition, taskType);
                Slot s = CreateConditionsSlot(t, allActions, allConstants);
                t.SetSlot(0, s);
                t.Iteration = iteration;
                t.usedActions = new bool[timelinePosition + 1];
                t.usedActions[timelinePosition] = true;
                subplansNew.Add(t);
            }
            return subplansNew;
        }

        /// <summary>
        /// Returns all possible fillings of an action with constant. 
        /// </summary>
        /// <param name="type"></param>
        /// <param name="allConstants"></param>
        /// <param name="allConstantTypes"></param>
        /// <param name="partialConst"></param>
        /// <param name="level"></param>
        /// <param name="solutions"></param>
        /// <returns></returns>
        protected List<List<Constant>> GetConstants(ActionType type, List<Constant> allConstants, List<ConstantType> allConstantTypes, List<Constant> partialConst, int level, 
            ref List<List<Constant>> solutions, CancellationToken cancellationToken)
        {
            if (cancellationToken.IsCancellationRequested) 
            {
                return null;
            }

            if (level == type.ActionTerm.Variables.Length)
            {
                solutions.Add(partialConst);
                partialConst = new List<Constant>();
                return solutions;
            }
            else
            {
                ConstantType desiredType = type.ActionTerm.Variables[level].Type;
                foreach (ConstantType ct in desiredType.DescendantTypes)
                {
                    foreach (Constant c in ct.Instances) //This goes through less constants then before. Before it went through all of them, now it goes through less. 
                    {
                        List<Constant> newPartialConst = new List<Constant>(partialConst);
                        newPartialConst.Add(c);
                        solutions = GetConstants(type, allConstants, allConstantTypes, newPartialConst, level + 1, ref solutions, cancellationToken);
                    }
                }

                return solutions;
            }
        }

        //this just takes the action as a term and then uses the actiontype to create proper conditions in timeline. 
        protected static Slot CreateConditionsSlot(Subplan t, List<ActionType> allActionTypes, List<Constant> allConstants)
        {
            Slot s = new Slot();
            s.a = t.TaskInstance;
            List<ActionType> all = allActionTypes.Where(x => x.ActionTerm.SameType(t.TaskInstance) == true).ToList();
            if (all.Count > 1)
            {
                Console.WriteLine("Error: There are multiple action types fitting this action.");
            }
            foreach (ActionType a in all)
            {
                if (a != null)
                {
                    s.PosPreConditions = CreateConditions(t.TaskInstance.Variables, a.PosPreConditions, allConstants);
                    s.NegPreConditions = CreateConditions(t.TaskInstance.Variables, a.NegPreConditions, allConstants);
                    s.PosPostConditions = CreateConditions(t.TaskInstance.Variables, a.PosPostConditions, allConstants);
                    s.NegPostConditions = CreateConditions(t.TaskInstance.Variables, a.NegPostConditions, allConstants);
                }

                // Added to allow "empty" actions such as "drive(loc1, loc1)" if they are allowed in domain description
                List<Term> toRemove = new List<Term>();
                foreach (var cond in s.NegPostConditions)
                {
                    // condition was already present in preconditions - it will be firstly removed and then added again in postconditions
                    if (s.PosPostConditions.Contains(cond) && s.PosPreConditions.Contains(cond))
                    {
                        toRemove.Add(cond);
                    }
                }
                foreach (var cond in toRemove)
                {
                    s.NegPostConditions.Remove(cond);
                }
            }
            return s;
        }

        /// <summary>
        /// Creates proper conditions from an action variables and conditions references.
        /// From input reader we get conditions as a name and a list of numbers for exmaple for action with parameters (a,b,c) and condition at(a,c).
        /// We get a condition at(0,2) (numbered form 0) this references teh parameters of the actions. Here it gets changed to teh actual conditions at(a,c).
        /// </summary>
        /// <param name="variables"></param>
        /// <param name="posPreConditions"></param>
        /// <returns></returns>
        protected static List<Term> CreateConditions(Constant[] variables, 
            List<Tuple<string, List<int>>> posPreConditions, List<Constant> allConstants)
        {
            List<Term> conditions = new List<Term>();
            string[] names = null;
           int counter = 1; 
            foreach (Tuple<string, List<int>> tupleCondition in posPreConditions)
            {
                names = null; 
                if (tupleCondition.Item1.Contains("!"))
                {
                    names = tupleCondition.Item1.Trim().Split('!');
                    counter = 1; 
                }
                Constant[] vars = new Constant[tupleCondition.Item2.Count];
                for (int i = 0; i < tupleCondition.Item2.Count; i++)
                {
                    int j = tupleCondition.Item2[i];
                    if (j == -2)
                    {
                        //This can only happen in two cases. Either this condition belongs to an exist condition or to an forall condition. 
                        //If the j=-2. This means its an exists condition.
                        vars[i] = null;
                    }
                    else if (j == -3)
                    {
                        //this action contains constants in condition parameters.
                        vars[i] = allConstants.Where(x => x.Name == names[counter]).FirstOrDefault();
                        counter++;
                    }
                    else
                    {
                        vars[i] = variables[tupleCondition.Item2[i]];
                    }

                }
                Term condition;
                if (names == null) condition = new Term(tupleCondition.Item1, vars);
                else condition = new Term(names[0], vars);
                conditions.Add(condition);
            }
            return conditions;
        }

        /// <summary>
        /// This is used to check exist conditions. 
        /// </summary>
        /// <param name="action"></param>
        /// <param name="s"></param>
        protected bool CheckNullConditions(List<Term> conditions, Term c)
        {
            if (c.Variables.Contains(null))
            {
                List<Term> sameNameCond = conditions.Where(x => x.EqualOrNull(c)).ToList(); //We found condition that satisfies this. 
                if (sameNameCond != null)
                {
                    foreach (Term sameNameC in sameNameCond)
                    {
                        if (!sameNameC.Variables.Contains(null)) return true;
                    }
                }
            }
            return false;
        }

        protected Constant[] ShortenVars(Constant[] vars)
        {
            List<Constant> vars2 = new List<Constant>();
            for (int i = 0; i < vars.Count(); i++)
            {
                if (vars[i] != null)
                {
                    vars2.Add(vars[i]);
                }
            }
            Constant[] vars3 = vars2.ToArray();
            return vars3;
        }

        protected static List<Slot> CreateEmptyTimeline(int j)
        {
            List<Slot> slots = new List<Slot>();
            for (int i = 0; i < j; i++)
            {
                Slot s = new Slot();
                slots.Add(s);
            }
            return slots;
        }

        /// <summary>
        /// Creates next megaslot from the previous one and actions that could be created there. It takes all the actions on previous slot and adds their positive effects. 
        /// </summary>
        /// <param name="megaslot"></param>
        /// <param name="newActions"></param>
        /// <returns></returns>
        protected Slot CreateNextMegaSlot(Slot megaslot, List<Subplan> newActions)
        {
            Slot newMegaslot = megaslot;
            foreach (Subplan action in newActions)
            {
                newMegaslot.PosPreConditions = UnifyConditions(newMegaslot.PosPreConditions, action.GetSlot(action.EndIndex - action.StartIndex).PosPostConditions);
            }
            return newMegaslot;
        }


        /// <summary>
        /// Checks whether this task is new. So whether there is no other task wiht the same name, variables and slots.  
        /// </summary>
        /// <param name="t"></param>
        /// <param name="allTasks"></param>
        /// <returns></returns>
        protected bool CheckNewness(Subplan t, List<Subplan> allTasks)
        {
            foreach (Subplan t1 in allTasks) // faster than LINQ version
            {
                if (t1.TaskInstance.Equals(t.TaskInstance) && t1.GetStartIndex() == t.GetStartIndex() && t1.GetEndIndex() == t.GetEndIndex())
                {
                    List<Term> t1terms = GetTerms(t1.Timeline);
                    List<Term> t2terms = GetTerms(t.Timeline);
                    if (t1terms.SequenceEqual(t2terms))
                    {
                        return false;
                    }
                }
            }
            return true;
        }

        /// <summary>
        /// Returns list of actions from list of slots. 
        /// </summary>
        /// <param name="timeline"></param>
        /// <returns></returns>
        protected List<Term> GetTerms(List<Slot> timeline)
        {
            List<Term> terms = new List<Term>();
            foreach (Slot s in timeline)
            {
                if (s == null) terms.Add(null);
                else terms.Add(s.a);
            }
            return terms;
        }

        /// <summary>
        /// Returns subplan if there is a subplan that spans over the whole plan and contains all actions. 
        /// This is then goal task. 
        /// </summary>
        /// <param name="plan"></param>
        /// <param name="subplans"></param>
        /// <returns></returns>
        protected Subplan FullSubplan(List<Term> plan, List<Subplan> subplans, int size)
        {
            List<Subplan> bigSubplans = GetSubPlans(0, size, subplans);
            bool valid = true;
            foreach (Subplan s in bigSubplans)
            {
                int i = 0;
                foreach (Slot sl in s.Timeline)
                {
                    if (!plan[i].Equals(sl.a)) valid = false;
                    i++;
                }
                if (valid) return s;
            }
            return null;
        }

        /// <summary>
        /// Returns applicable rules. Rules that have all subtasks present so most likely can be created. 
        /// </summary>
        /// <param name="plan"></param>
        /// <param name="newTasks"></param>
        /// <param name="iteration"></param>
        /// <returns></returns>
        protected List<Rule> GetApplicableRules(List<Term> plan, List<Subplan> newTasks, int iteration)
        {
            List<Rule> readyRules = new List<Rule>();
            foreach (Subplan t in newTasks)
            {
                t.AddToTaskType();
                TaskType taskType = t.TaskType;
                List<Rule> taskRules = taskType.ActivateRules(iteration);
                readyRules.AddRange(taskRules);
            }
            return readyRules;
        }

        internal bool CheckValidity(List<Slot> timeline)
        {
            foreach (Slot s in timeline)
            {
                if (s != null && !s.IsValid()) 
                    return false;
            }
            return true;
        }

        /// <summary>
        /// Propagates pre conditions to post conditions within 1 slot. 
        /// </summary>
        /// <param name="s"></param>
        protected static void SelfPropagate(Slot s)
        {
            List<Term> c1 = RemoveConditions(s.PosPreConditions, s.NegPostConditions);
            s.PosPostConditions = UnifyConditions(s.PosPostConditions, c1);
        }


        /// <summary>
        /// This is basic propagation. 
        /// It is used when creating megaslot and at the start when we create prefix Timeline. 
        /// Note that prefix Timeline also uses a different propagation though it's called propagation there. 
        /// </summary>
        /// <param name="timeline"></param>
        protected void Propagate(ref List<Slot> timeline)
        {
            for (int i = 0; i < timeline.Count - 1; i++)
            {
                Slot slot1 = timeline[i];
                Slot slot2 = timeline[i + 1];
                //Left To Right
                if (slot1 != null) //if slot1 is null there is nothing to propagate. 
                {

                    //If the second slot was null. We must now add it preconditions if there are any but no action. 
                    if (slot2 == null) slot2 = new Slot();
                    slot2.PosPreConditions = UnifyConditions(slot2.PosPreConditions, slot1.PosPostConditions);
                    slot2.NegPreConditions = UnifyConditions(slot2.NegPreConditions, slot1.NegPostConditions);
                    timeline[i + 1] = slot2;

                    //Action
                    if (slot1.a != null)
                    {
                        List<Term> c1 = RemoveConditions(slot1.PosPreConditions, slot1.NegPostConditions);
                        slot2.PosPreConditions = UnifyConditions(slot2.PosPreConditions, c1); //These conditions were true before previous state and were not changed, so they must remain true still. 
                        c1 = RemoveConditions(slot1.NegPreConditions, slot1.PosPostConditions);
                        slot2.NegPreConditions = UnifyConditions(slot2.NegPreConditions, c1); //These conditions cannot be true before previous state and were not changed, so they must remain not true still
                    }
                }

            }
            //Right To Left
            for (int i = timeline.Count - 1; i > 0; i--)
            {
                Slot slot1 = timeline[i - 1]; //First slot
                Slot slot2 = timeline[i]; //second slot
                //Right To Left
                if (slot1 == null)
                {
                    slot1 = new Slot();
                    timeline[i - 1] = slot1;
                }
                if (slot2 == null)
                {
                    slot2 = new Slot();
                    timeline[i] = slot2;
                }
                if (slot1.a != null)
                {
                    List<Term> c1 = RemoveConditions(slot2.PosPreConditions, slot1.PosPostConditions);
                    slot1.PosPreConditions = UnifyConditions(slot1.PosPreConditions, c1); //These conditions were true in the next state and were not created by this action so they must have been true before this state as well.
                    c1 = RemoveConditions(slot2.NegPreConditions, slot1.NegPostConditions);
                    slot1.NegPreConditions = UnifyConditions(slot1.NegPreConditions, c1); //Same as above just for false. 
                }

            }
        }
        /// <summary>
        /// Second propagation used for tasks that have at least one slot of megaslots. 
        /// We only propagate towards any slot in already prefixed timeline. Once we get there we simply check if all conditions are present if not this new task is invalid. 
        /// We do not need to propagate on normal slot as the prefix Timeline already did that for us. 
        /// </summary>
        /// <param name="timeline"></param>
        internal virtual bool MegaslotPropagate(ref List<Slot> timeline, int prefixTimelineLength, int startIndex)
        {                                                                                                  

            for (int j = 0; j < timeline.Count - 1; j++)
            {
                //There is no need to propagate within the prefixTimeline as everything is propagated there already. So we only start at the last prefixTimeline slot which is
                //at prefixTimelinelength -1.
                if (j + startIndex >= prefixTimelineLength - 1)
                {
                    Slot slot1 = timeline[j];
                    Slot slot2 = timeline[j + 1];
                    //Left To Right
                    if (slot1 != null) //if slot1 is null there is nothing to propagate. 
                    {

                        //If the second slot was null. We must now add it preconditions if there are any but no action. 
                        if (slot2 == null) slot2 = new Slot();
                        slot2.PosPreConditions = UnifyConditions(slot2.PosPreConditions, slot1.PosPostConditions);
                        slot2.NegPreConditions = UnifyConditions(slot2.NegPreConditions, slot1.NegPostConditions);
                        timeline[j + 1] = slot2;

                        //Action
                        if (slot1.a != null)
                        {
                            List<Term> c1 = RemoveConditions(slot1.PosPreConditions, slot1.NegPostConditions);
                            slot2.PosPreConditions = UnifyConditions(slot2.PosPreConditions, c1); //These conditions were true before previous state and were not changed, so they must remain true still. 
                            c1 = RemoveConditions(slot1.NegPreConditions, slot1.PosPostConditions);
                            slot2.NegPreConditions = UnifyConditions(slot2.NegPreConditions, c1); //These conditions cannot be true before previous state and were not changed, so they must remain not true still
                        }
                    }
                }

            }
            //Right To Left
            int i = timeline.Count - 1;
            bool stop = false;
            while (i > 0 && !stop)
            {
                Slot slot1 = timeline[i - 1]; //First slot
                Slot slot2 = timeline[i]; //second slot
                //Right To Left
                if (slot1 == null)
                {
                    slot1 = new Slot();
                    timeline[i - 1] = slot1;
                }
                if (slot2 == null)
                {
                    slot2 = new Slot();
                    timeline[i] = slot2;
                }
                if (slot1.a != null || i <= prefixTimelineLength - startIndex) //Either this is in megaslots and this slot and the previous slot has an action so we propagate our preconditions forward
                                                                               //or this is already a prefixed slot and then we simply check if all our preconditions are valid. If not then this task is invalid. 
                {
                    List<Term> c1 = RemoveConditions(slot2.PosPreConditions, slot1.PosPostConditions);
                    //This is prefixed slot so we simply check if our conditions are fulfilled. 
                    if (i <= prefixTimelineLength - startIndex)
                    {
                        if (c1.Any())
                        {
                            return false;
                        }
                        else
                        {
                            //We got to the prefix part and everything is valid. We may stop propagating
                            stop = true;
                        }
                    }
                    if (slot1.a != null) slot1.PosPreConditions = UnifyConditions(slot1.PosPreConditions, c1); //These conditions were true in the next state and were not created by this action so they must have been true before this state as well.
                    c1 = RemoveConditions(slot2.NegPreConditions, slot1.NegPostConditions);
                    //With negative we don't need to do the check in prefixTimeline because this is checked in checkvalidity. 
                    if (slot1.a != null) slot1.NegPreConditions = UnifyConditions(slot1.NegPreConditions, c1); //Same as above just for false.
                }
                i--;

            }
            return true;
        }

        /// <summary>
        /// Checks precodnitions of task if its in normal slot. If its in megaslot it just adds it and it will be propagated forward. 
        /// The timeline belongs to this task so the numbers from conditions are pointing straight to slots.
        /// </summary>
        /// <param name="timeline"></param>
        /// <param name="posPropositions"></param>
        /// <param name="negPropositions"></param>
        internal static bool ApplyPre(List<Slot> timeline, List<Tuple<int, Term>> posPropositions,
            List<Tuple<int, Term>> negPropositions, int startIndex,
            int prefixLength)
        {
            foreach (Tuple<int, Term> tupleCondition in posPropositions)
            {
                Slot slot;
                if (tupleCondition.Item1 == -1)
                {
                    //we take this as the fact that it must be true before the whole task so on startindex slot. 
                    slot = timeline.FirstOrDefault(v => v != null);
                }
                else slot = timeline[tupleCondition.Item1];
                Term t = tupleCondition.Item2;
                if (!slot.PosPreConditions.Contains(t))
                {
                    //If this is in prefix slot than this is false and this task will not be valid. Because I know every condition in prefix slot already and this condition is not valid.   
                    //However if this is in a megaslot then i must propagate the conditions forward. So that's okay. 
                    if (startIndex + tupleCondition.Item1 >= prefixLength)
                    {
                        //This is a megaslot so simply adding the condition is correct.
                        slot.PosPreConditions.Add(t);
                    }
                    else
                    {
                        return false;
                    }
                }
            }
            foreach (Tuple<int, Term> tupleCondition in negPropositions)
            {
                Slot slot;
                if (tupleCondition.Item1 == -1)
                {
                    //we take this as the fact that it must be true before the whole task so on startindex slot. 
                    slot = timeline.FirstOrDefault(v => v != null);
                }
                else slot = timeline[tupleCondition.Item1];
                Term t = tupleCondition.Item2;
                if (!slot.NegPreConditions.Contains(t))
                {
                    if (startIndex + tupleCondition.Item1 >= prefixLength)
                    {
                        slot.NegPreConditions.Add(t);
                    }

                    else if (slot.PosPreConditions.Contains(t))
                    {
                        //The conditons that shouldnt be true is so its definitely false. 
                        return false;
                    }
                    else
                    {
                        //It's not in negative preconditions, but the conditions is also not present on positive conditions, which could happen if this is an empty task.
                        //The empty task is a something on top of a normal prefix plan so we will propagate it here like if it was a megaslot.
                        slot.NegPreConditions.Add(t);
                    }
                }
            }
            return true;
        }

        /// <summary>
        /// Adds post conditions to slots from rule. 
        /// </summary>
        /// <param name="timeline"></param>
        /// <param name="posConditions"></param>
        /// <param name="negConditions"></param>
        internal void ApplyPost(List<Slot> timeline, List<Tuple<int, Term>> posConditions, List<Tuple<int, Term>> negConditions)
        {
            foreach (Tuple<int, Term> tupleCondition in posConditions)
            {
                Slot slot = timeline[tupleCondition.Item1];
                Term t = tupleCondition.Item2;
                if (!slot.PosPostConditions.Contains(t)) slot.PosPostConditions.Add(t);
            }
            foreach (Tuple<int, Term> tupleCondition in negConditions)
            {
                Slot slot = timeline[tupleCondition.Item1];
                Term t = tupleCondition.Item2;
                if (!slot.NegPostConditions.Contains(t)) slot.NegPostConditions.Add(t);
            }
        }

        /// <summary>
        /// Applies between constraints to all slots between the starting and the ending slot. What if the between constraint should only apply to some of them???
        /// </summary>
        /// <param name="timeline"></param>
        /// <param name="posConditions"></param>
        /// <param name="negConditions"></param>
        internal bool ApplyBetween(List<Slot> timeline, List<Tuple<int, int, Term>> posConditions, List<Tuple<int, int, Term>> negConditions, int startIndex, int prefixLength)
        {
            foreach (Tuple<int, int, Term> tupleCondition in posConditions)
            {
                for (int i = tupleCondition.Item1 + 1; i <= tupleCondition.Item2; i++)
                {
                    Slot slot = timeline[i];
                    Term t = tupleCondition.Item3;
                    if (!slot.PosPreConditions.Contains(t))
                    {
                        //If this is in prefix slot than this is false and this task will not be valid. Because I know every condition in prefix slot already and this condition is not valid.   
                        //However if this is in a megaslot then i must propagate the conditions forward. So that's okay. 
                        if (startIndex + tupleCondition.Item1 >= prefixLength)
                        {
                            //This is a megaslot so simply adding the condition is correct.
                            slot.PosPreConditions.Add(t);
                        }
                        else
                        {
                            return false;
                        }
                    }
                }
            }
            foreach (Tuple<int, int, Term> tupleCondition in posConditions)
            {
                for (int i = tupleCondition.Item1; i <= tupleCondition.Item2; i++)
                {
                    Slot slot = timeline[i];
                    Term t = tupleCondition.Item3;
                    if (!slot.NegPreConditions.Contains(t))
                    {
                        //If this is in prefix slot than this is false and this task will not be valid. Because I know every condition in prefix slot already and this condition is not valid.   
                        //However if this is in a megaslot then i must propagate the conditions forward. So that's okay. 
                        if (startIndex + tupleCondition.Item1 >= prefixLength)
                        {
                            //This is a megaslot so simply adding the condition is correct.
                            slot.NegPreConditions.Add(t);
                        }
                        else
                        {
                            return false;
                        }
                    }
                }
            }
            return true;
        }



        /// <summary>
        /// Merges subtasks. Returns a subplan representing the new timeline. 
        /// Merges empty subplan with full subplan. 
        /// 
        /// </summary>
        /// <param name="subtasks">List of subtasks which it should merge</param>
        /// <param name="name">Name of new task</param>
        /// <returns></returns>
        internal Subplan MergePlans(List<Subplan> subtasks, Term actName, TaskType mainTaskType, List<Slot> prefixTimeline)
        {
            double newStartIndex;
            double newEndIndex;



            newStartIndex = subtasks.OrderBy(p => p.StartIndex).First().StartIndex;
            newEndIndex = subtasks.OrderBy(p => p.EndIndex).Last().EndIndex;
            Subplan newSubplan = new Subplan(actName, newStartIndex, newEndIndex, mainTaskType);
            for (double i = Math.Ceiling(newStartIndex); i <= Math.Ceiling(newEndIndex); i++)
            {
                foreach (Subplan subplan in subtasks)
                {
                    foreach (var h in subplan.History)
                    {
                        newSubplan.AddToHistory(h);
                    }

                    if (i >= Math.Ceiling(subplan.StartIndex) && i <= Math.Ceiling(subplan.EndIndex)) //if i is smaller than subplan start index then i dont care about this subtask now 
                    {
                        //If I have two s
                        double slotNum = 0;
                        slotNum = i - Math.Ceiling(subplan.StartIndex); //If start index is for exmaple 4,5 this rounds up to 5.
                        Slot s = subplan.GetSlot(slotNum);
                        double slotNum2 = 0;
                        slotNum2 = i - Math.Ceiling(newStartIndex); //this is slot of the new subplan. Now here we just use i as reference. 
                        Slot s2 = newSubplan.GetSlot(slotNum2);
                        if (s != null)
                        {
                            Slot s3 = MergeSlots(s, s2, (int)Math.Ceiling(i), prefixTimeline);
                            if (s3 == null) 
                                return null;
                            newSubplan.SetSlot(slotNum2, s3);
                        }
                    }
                }
                if (newSubplan.GetSlot(i - Math.Ceiling(newStartIndex)) == null && i < prefixTimeline.Count())
                {
                    Slot s = prefixTimeline[(int)Math.Ceiling(i)];
                    s.a = null;
                    newSubplan.SetSlot(i - Math.Ceiling(newStartIndex), s);
                }

                ///merge slots at same position.                
            }
            return newSubplan;
        }

        /// <summary>
        /// Merges two slot on same position. If the position is within the prefix length it will take the slot from the prefixTimeline. If not it will merge normally. 
        /// </summary>
        /// <param name="s"></param>
        /// <param name="s2"></param>
        /// <param name="i"></param>
        /// <returns></returns>
        protected Slot MergeSlots(Slot s, Slot s2, int i, List<Slot> prefixTimeline)
        {
            Slot s3;
            if (prefixTimeline != null && prefixTimeline.Count > 0 && i < prefixTimeline.Count)
            {
                s3 = new Slot(prefixTimeline[i]);
                if (s != null) s3.a = s.a;
                else 
                    s3.a = null;
            }
            else s3 = new Slot(s);
            if (s2 != null)
            {
                if (s.a == null && s2.a == null)
                { //This is a slot without action so 
                    s3.a = null;
                }
                else if (s.a == null || s.a.Name == null || s.a.Name == Subplan.DUMMY_EMPTY_ACTION_NAME) 
                    s3.a = s2.a; // Action from first slot is empty so take action from second slot.  
                else if (s2.a == null || s2.a.Name == null || s2.a.Name == Subplan.DUMMY_EMPTY_ACTION_NAME) 
                    s3.a = s.a;
                else return null; //both slots have filled action. 
            }
            if (prefixTimeline != null && i < prefixTimeline.Count())
            {
                MergeConditions(s3, s, s2);
            }
            else
            {
                MergeConditions(s3, s3, s2);
                MergeConditions(s3, s, s3);
            }
            return s3;
        }
        /// <summary>
        /// Unifies same type of conditions in slot s2 and s1 and puts it itnto he right type of condition in s3 like this.
        /// s3.PosPreConditions = UnifyConditions(s3.PosPreConditions, s2.PosPreConditions);
        /// </summary>
        /// <param name="s3"></param>
        /// <param name="s2"></param>
        /// <param name="s1"></param>
        protected void MergeConditions(Slot s3, Slot s1, Slot s2)
        {
            if (s1 != null && s2 != null) s3.PosPreConditions = UnifyConditions(s1.PosPreConditions, s2.PosPreConditions);
            if (s1 != null && s2 != null) s3.NegPreConditions = UnifyConditions(s1.NegPreConditions, s2.NegPreConditions);
            if (s1 != null && s2 != null) s3.PosPostConditions = UnifyConditions(s1.PosPostConditions, s2.PosPostConditions);
            if (s1 != null && s2 != null) s3.NegPostConditions = UnifyConditions(s1.NegPostConditions, s2.NegPostConditions);
        }

        /// <summary>
        /// Returns list of unified conditions. 
        /// </summary>
        /// <param name="c1"></param>
        /// <param name="c2"></param>
        /// <returns></returns>
        protected static List<Term> UnifyConditions(List<Term> c1, List<Term> c2)
        {
            if ((c1 == null && c2 == null) || (!c1.Any() && !c2.Any())) return new List<Term>(); //if both lists are empty return empty list as well.
            List<Term> c3;
            if (c1 != null) c3 = new List<Term>(c1);
            else c3 = new List<Term>(c2);
            foreach (Term c in c2)
            {
                if (!c1.Contains(c)) c3.Add(c);
            }
            return c3;
        }




        /// <summary>
        /// Takes conditons form second list and removes them from first list.        /// 
        /// </summary>
        /// <param name="c1"></param>
        /// <param name="c2"></param>
        /// <returns></returns>
        protected static List<Term> RemoveConditions(List<Term> c1, List<Term> c2)
        {
            List<Term> c3 = new List<Term>(c1);
            foreach (Term c in c2)
            {
                if (c1.Contains(c)) c3.RemoveAll(x => x.Equals(c)); 
            }
            return c3;
        }

        /// <summary>
        /// Returns task that have designated start index. Their end index is the same as given end index. 
        /// </summary>
        /// <param name="StartIndex"></param>
        /// <param name="EndIndex"></param>
        /// <returns></returns>
        protected List<Subplan> GetSubPlans(int StartIndex, int EndIndex, List<Subplan> plans)
        {
            return plans.Where(x => x.StartIndex == StartIndex && x.EndIndex == EndIndex).ToList();
        }

        /// <summary>
        /// Returns task that have designated end index. 
        /// </summary>
        /// <param name="StartIndex"></param>
        /// <param name="EndIndex"></param>
        /// <returns></returns>
        protected List<Subplan> GetSubPlans(int EndIndex, List<Subplan> plans)
        {
            return plans.Where(x => x.EndIndex == EndIndex).ToList();
        }

        internal static TaskType FindTaskType(Term a, List<TaskType> allTaskTypes)
        {
            foreach (TaskType t in allTaskTypes)
            {
                if (t.Name.Equals(a.Name) && t.NumOfVariables == a.Variables.Length) return t;
            }
            return null;
        }
    }
}
