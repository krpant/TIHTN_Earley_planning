using System;
using System.Collections.Generic;
using System.Linq;

namespace PlanRecognitionNETF
{
    /// <summary>
    /// Represents a method in domain file. 
    /// </summary>
    class Rule
    {
        public string Name { get; set; } 
        //the main task of this method. 
        public TaskType MainTaskType;
        //References to subtsaks
        public TaskType[] TaskTypeArray;
        bool[] TaskTypeActivationArray;
        /// <summary>
        /// For each activated subtask this contains the iteration number of activation. 
        /// </summary>
        int[] TaskTypeActivationIteratiobnArray;
        int[] TaskMinLegthArray; //This is set to fixed 100000. 
        int[] TaskMaxLegthArray; //This is set to fixed -1. 
        int ActivatedTasks;
        /// <summary>
        /// One list represents one task and the numbers in him say which variable of the main task this corresponds to. So for example for rule:
        /// Transfer(L1,C,R,L2):-Load(C,L1,R),Move(R,L1,L2),Unload(C,L2,R)
        /// The array looks like this{(1,0,2),(2,0,3),(1,3,2)} If the subtasks contain a constant that is not in the main task we give it -1.
        /// 
        /// </summary>
        public List<int>[] ArrayOfReferenceLists;
        /// <summary>
        /// The first int says to which of the rule's subtasks this applies to,the string is the name of the condition and the list of ints i the references to the action variables.
        /// So for example for condition at(C,L1) for load(C,L1,R)  we
        /// have tuple (0,at,(0,1))
        /// If it applies to the whole subtask then it has -1. so (-1,at,(0,1))
        /// </summary>
        public List<Tuple<int, String, List<int>>> posPreConditions;
        public List<Tuple<int, String, List<int>>> negPreConditions;
        /// <summary>
        /// The first int says to which of the rule's subtasks this applies to,the string is the name of the condition and the list of ints i the references to the action variables.
        /// So for example for condition at(C,L1) for load(C,L1,R)  we
        /// have tuple (0,at,(0,1))
        /// </summary>
        public List<Tuple<int, String, List<int>>> posPostConditions;
        public List<Tuple<int, String, List<int>>> negPostConditions;
        /// <summary>
        /// For between condition, we have two ints representing which actions they are related too. Then name of condition. Then list of ints representing to which variables they are related to.
        /// 
        /// So for exmaple for condition on(R,C) between Load(C,L1,R) and Unload(C,L2,R) and Rule(C,L1,L2,R) where load is its first subtask and unload its third it would be this: (0,2,on,(3,0))
        /// </summary>
        public List<Tuple<int, int, String, List<int>>> posBetweenConditions;
        public List<Tuple<int, int, String, List<int>>> negBetweenConditions;

        public List<Tuple<int, int>> orderConditions;

        //Refrences from main task to allVars.
        public List<int> MainTaskReferences;

        /// <summary>
        /// All variables used in this rule (in main task or any subtask)
        /// </summary>
        public List<String> AllVars { get; set; } = new List<string>();
        public List<ConstantType> AllVarsTypes = new List<ConstantType>(); //Types as read in input for this rule. The actual constants used might have some children type to this.  
        /// <summary>
        /// Represents the number of subtask that are after this particual subtask based on ordering.         /// 
        /// </summary>
        public int[] numOfOrderedTasksAfterThisTask;
        /// <summary>
        /// Same as after this task except for Before. 
        /// </summary>
        public int[] numOfOrderedTasksBeforeThisTask;

        public int[] minOrderedTaskPosition; //The minimum lentgh of task before this task
        public int[] minOrderedTaskPositionAfter; //The minimum length of tasks after this task.So this is the maximum end index of my task.

        public Rule()
        {
            posPreConditions = new List<Tuple<int, string, List<int>>>();
            negPreConditions = new List<Tuple<int, string, List<int>>>();
            posPostConditions = new List<Tuple<int, string, List<int>>>();
            negPostConditions = new List<Tuple<int, string, List<int>>>();
            posBetweenConditions = new List<Tuple<int, int, string, List<int>>>();
            negBetweenConditions = new List<Tuple<int, int, string, List<int>>>();

        }

        //It is given everything it will be given. It should fill up the rest.
        //For example must fill reference list and maintaskreferences.
        internal void Finish(List<List<int>> refList)
        {
            TaskTypeActivationArray = new bool[TaskTypeArray.Count()];
            TaskTypeActivationIteratiobnArray = new int[TaskTypeArray.Count()];
            TaskMinLegthArray = Enumerable.Repeat(100000, TaskTypeArray.Count()).ToArray();
            TaskMaxLegthArray = Enumerable.Repeat(-1, TaskTypeArray.Count()).ToArray();
            minOrderedTaskPositionAfter = new int[TaskTypeArray.Count()];
            minOrderedTaskPosition = new int[TaskTypeArray.Count()];
            ArrayOfReferenceLists = refList.ToArray();
            if (posPreConditions == null) posPreConditions = new List<Tuple<int, string, List<int>>>();
            if (negPreConditions == null) negPreConditions = new List<Tuple<int, string, List<int>>>();
            if (posPostConditions == null) posPostConditions = new List<Tuple<int, string, List<int>>>();
            if (negPostConditions == null) negPostConditions = new List<Tuple<int, string, List<int>>>();
            if (posBetweenConditions == null) posBetweenConditions = new List<Tuple<int, int, string, List<int>>>();
            if (negBetweenConditions == null) negBetweenConditions = new List<Tuple<int, int, string, List<int>>>();
            //main task reference list is done elsewhere.            
        }

        /// <summary>
        /// Calculates how many subtasks are after each task. 
        /// </summary>
        private void CalculateActionsAfter()
        {
            numOfOrderedTasksAfterThisTask = new int[TaskTypeArray.Length];
            numOfOrderedTasksBeforeThisTask = new int[TaskTypeArray.Length];
            if (orderConditions != null && orderConditions.Any())
            {
                List<List<int>> listAfter = CreateListsOfTasks(true);
                List<List<int>> listBefore = CreateListsOfTasks(false);
                for (int i = 0; i < listAfter.Count; i++)
                {
                    List<int> tasksAfter = CreateListFor(i, listAfter);
                    tasksAfter = tasksAfter.Distinct().ToList();
                    numOfOrderedTasksAfterThisTask[i] = tasksAfter.Count();
                    List<int> tasksBefore = CreateListFor(i, listBefore);
                    numOfOrderedTasksBeforeThisTask[i] = tasksBefore.Distinct().Count();
                }
            }
        }

        public Term FillMainTaskFromAllVarsReturnTerm(List<Constant> myAllVars)
        {
            String taskName = MainTaskType.Name;
            Constant[] vars = new Constant[MainTaskReferences.Count];
            for (int i = 0; i < MainTaskReferences.Count; i++)
            {
                vars[i] = myAllVars[MainTaskReferences[i]]; //Here we give the type from the task but we should give it the type of the constant.                 
            }
            Term term = new Term(taskName, vars);
            return term;
        }

        /// <summary>
        /// Calculates tasks minimum and maximum position in rule subtasks. 
        /// </summary>
        private void CalculateTaskMinMaxPosition()
        {
            if (orderConditions != null && orderConditions.Any())
            {
                List<List<int>> listAfter = CreateListsOfTasks(true);
                List<List<int>> listBefore = CreateListsOfTasks(false);
                for (int i = 0; i < listAfter.Count; i++)
                {
                    List<int> tasksAfter = CreateListFor(i, listAfter);
                    tasksAfter = tasksAfter.Distinct().ToList();
                    int sum = 0;
                    for (int j = 0; j < tasksAfter.Count; j++)
                    {
                        sum = sum + TaskMinLegthArray[tasksAfter[j]];
                    }
                    minOrderedTaskPositionAfter[i] = sum;
                    List<int> tasksBefore = CreateListFor(i, listBefore);
                    sum = 0;
                    for (int j = 0; j < tasksBefore.Count; j++)
                    {
                        sum = sum + TaskMinLegthArray[tasksBefore[j]];
                    }
                    minOrderedTaskPosition[i] = sum;

                }
            }
        }


        /// <summary>
        /// Thsi just makes it easier to calculate how many tasks are after a task. 
        /// </summary>
        /// <param name="i"></param>
        /// <param name="listAfter"></param>
        /// <returns></returns>
        private List<int> CreateListFor(int i, List<List<int>> listAfter)
        {
            List<int> tasksAfter = listAfter[i].ToList();
            foreach (int l in listAfter[i])
            {
                tasksAfter.AddRange(CreateListFor(l, listAfter));
            }
            return tasksAfter;
        }

        /// <summary>
        /// True means tasks after, false means tasks before. 
        /// </summary>
        /// <returns></returns>
        private List<List<int>> CreateListsOfTasks(bool after)
        {
            List<List<int>> indexOfTasksAfter = new List<List<int>>(TaskTypeArray.Length); //Represents the index of tasks that are ordered with this task. Only immediate level. Meaning if I have ordering 1<2 and 2<3. INdex 1 onlz has 3 there. 
            for (int i = 0; i < TaskTypeArray.Length; i++) indexOfTasksAfter.Add(null);
            for (int i = 0; i < TaskTypeArray.Length; i++)
            {
                List<int> tupledWith;
                if (after)
                {
                    TupleWithXFirst(i, out tupledWith);
                    indexOfTasksAfter[i] = tupledWith;
                }
                else
                {
                    TupleWithXLast(i, out tupledWith);
                    indexOfTasksAfter[i] = tupledWith;
                }
            }
            return indexOfTasksAfter;
        }

        /// <summary>
        /// Returns the number of ordering tuples where this number is first.
        /// In the tupledWithList returns the indexof tasks it's ordered with. 
        /// </summary>
        /// <returns></returns>
        private int TupleWithXFirst(int index, out List<int> tupledWith)
        {
            List<Tuple<int, int>> rightTuples = orderConditions.Where(x => x.Item1 == index).ToList();
            tupledWith = rightTuples.Select(x => x.Item2).ToList();
            return tupledWith.Count;
        }

        /// <summary>
        /// Returns the number of ordering tuples where this number is first.
        /// In the tupledWithList returns the indexof tasks it's ordered with. 
        /// </summary>
        /// <returns></returns>
        private int TupleWithXLast(int index, out List<int> tupledWith)
        {
            List<Tuple<int, int>> rightTuples = orderConditions.Where(x => x.Item2 == index).ToList();
            tupledWith = rightTuples.Select(x => x.Item1).ToList();
            return tupledWith.Count;
        }


        /// <summary>
        /// Returns true if after activating this task the rule is ready to be used. 
        /// Int j says how many instance maximum I can fill in this rule. 
        /// </summary>
        /// <param name="t"></param>
        /// <returns></returns>
        public bool Activate(TaskType t, int j, int iteration)
        {
            List<int> occurences = Enumerable.Range(0, TaskTypeArray.Count()).Where(p => TaskTypeArray[p] == t).ToList();
            if (occurences.Count > j) return false; //I cant fill all instances of this subtask in this rule so it definitely canot be used.
            else
            {
                foreach (int i in occurences)
                {
                    if (!TaskTypeActivationArray[i]) ActivatedTasks++; //If this activated the task (as in it was not ready before) it should increase the activated task counter.
                    TaskTypeActivationArray[i] = true;
                    TaskTypeActivationIteratiobnArray[i] = iteration; //Iterations always increases over time. So if I had a different task here in iteration 4, that's fine now I rewrite it to 6.
                    if (t.minTasklength < TaskMinLegthArray[i]) TaskMinLegthArray[i] = t.minTasklength;
                }
                if (TaskMinLegthArray.Contains(100000) == false)
                {
                    int sum = TaskMinLegthArray.Sum();
                    bool changed = false;
                    changed = MainTaskType.SetMinTaskLengthIfSmaller(sum);
                    if (changed) CalculateTaskMinMaxPosition();

                }
            }

            return (ActivatedTasks == TaskTypeActivationArray.Length);
        }
        internal List<List<int>> GetExplicitSubtaskOrdering()
        {
            if (TaskTypeArray == null || TaskTypeArray.Length == 0)
            {
                return null;
            }
            else if (TaskTypeArray.Length == 1)
            {
                return new List<List<int>> { new List<int> { 0 } };
            }

            List<HashSet<int>> setsBefore;
            if (orderConditions == null)
            {
                setsBefore = new List<HashSet<int>>();
                for (int i = 0; i < TaskTypeArray.Length; i++)
                {
                    setsBefore.Add(new HashSet<int>());
                }
            }
            else
            {
                setsBefore = GetSetsBefore();
            }
            return GenerateOrderings(setsBefore);
        }

        List<List<int>> GenerateOrderings(List<HashSet<int>> setsBefore)
        {
            var ready = new HashSet<int>();
            for (int i = 0; i < setsBefore.Count; i++)
            {
                HashSet<int> set = setsBefore[i];
                if (set.Count == 0)
                {
                    ready.Add(i);
                }
            }

            GenerateAllOrderConstrains(setsBefore);
            List<List<int>> result = new List<List<int>>();
            GenerateOrderings(new List<int>(), setsBefore, ready, result);
            return result;
        }

        private void GenerateAllOrderConstrains(List<HashSet<int>> setsBefore)
        {
            bool changed = true;
            while (changed)
            {
                changed = false;
                foreach (var set in setsBefore)
                {
                    HashSet<int> toAdd = new HashSet<int>();
                    foreach (var s in set)
                    {
                        foreach (var subtaskBeforeS in setsBefore[s])
                        {
                            if (!set.Contains(subtaskBeforeS))
                            {
                                toAdd.Add(subtaskBeforeS);
                            }
                        }
                    }
                    if (toAdd.Count > 0)
                    {
                        changed = true;
                        foreach (var subtask in toAdd)
                        {
                            set.Add(subtask);
                        }
                    }
                }
            }
        }

        void GenerateOrderings(List<int> currentOrdering, List<HashSet<int>> setsBefore, HashSet<int> readySubtasks, List<List<int>> allPossibleOrderings)
        {
            if (currentOrdering.Count == TaskTypeArray.Length)
            {
                allPossibleOrderings.Add(new List<int>(currentOrdering));
            }
            else if (readySubtasks.Count > 0)
            {
                foreach (int nextSubtask in readySubtasks)
                {
                    HashSet<int> newReadySubtasks = new HashSet<int>(readySubtasks);
                    currentOrdering.Add(nextSubtask);
                    newReadySubtasks.Remove(nextSubtask);

                    List<int> tasksAfterThisTask = new List<int>();
                    for (int i = 0; i < setsBefore.Count; i++)
                    {
                        if (!currentOrdering.Contains(i))
                        {
                            HashSet<int> set = setsBefore[i];
                            if (set.Contains(nextSubtask))
                            {
                                set.Remove(nextSubtask);
                                tasksAfterThisTask.Add(i);
                            }
                            if (set.Count == 0)
                            {
                                newReadySubtasks.Add(i);
                            }
                        }
                    }

                    GenerateOrderings(currentOrdering, setsBefore, newReadySubtasks, allPossibleOrderings);

                    currentOrdering.RemoveAt(currentOrdering.Count - 1);
                    foreach (int i in tasksAfterThisTask)
                    {
                        setsBefore[i].Add(nextSubtask);
                        if (setsBefore[i].Count == 1)
                        {
                            newReadySubtasks.Remove(i);
                        }
                    }
                }
            }
        }

        List<HashSet<int>> GetSetsBefore()
        {
            var list = new List<HashSet<int>>();
            for (int i = 0; i < TaskTypeArray.Length; i++)
            {
                list.Add(new HashSet<int>());
            }
            foreach (var constraint in orderConditions)
            {
                list[constraint.Item2].Add(constraint.Item1);
            }
            return list;
        }

        /// <summary>
        /// Adds order conditions to orderconditions of this rule. 
        /// </summary>
        /// <param name="item31"></param>
        /// <param name="item32"></param>
        internal void AddOrderCondition(int item31, int item32)
        {
            if (orderConditions == null) orderConditions = new List<Tuple<int, int>>();
            Tuple<int, int> t = new Tuple<int, int>(item31, item32);
            orderConditions.Add(t);
        }

        /// <summary>
        /// Order is fixed from the position of subtasks. This creates the orderConditions.  
        /// </summary>
        internal void CreateOrder()
        {
            orderConditions = new List<Tuple<int, int>>();
            for (int i = 0; i < TaskTypeArray.Length - 1; i++)
            {
                int j = i + 1;
                Tuple<int, int> t = new Tuple<int, int>(i, j);
                orderConditions.Add(t);
            }
            CalculateActionsAfter();
        }

        /// <summary>
        /// Returns combination of taskInstances from task types that work with this rule.
        /// It will first fix the new subtasks (the ones we got in the latest iteration) and then tries to fill out the rest.
        /// </summary>
        public List<RuleInstance> GetRuleInstances(int planSize, List<Constant> allConstants, int iteration)
        {
            Constant[] nullArray = new Constant[MainTaskType.NumOfVariables];
            for (int i = 0; i < nullArray.Length; i++)
            {
                nullArray[i] = null;
            }
            Term t = new Term(MainTaskType.Name, nullArray); //nullarray is filled with nulls. 
            Subplan MainTaskInstance = new Subplan(t, GetMin(TaskTypeActivationArray), GetMax(TaskTypeActivationArray), MainTaskType);
            List<Constant> emptyVars = FillFromAllVars(allConstants);
            List<Tuple<Subplan, List<Subplan>, List<Constant>>> ruleVariants = new List<Tuple<Subplan, List<Subplan>, List<Constant>>>();
            for (int i = 0; i < TaskTypeActivationIteratiobnArray.Length; i++)
            {
                if (TaskTypeActivationIteratiobnArray[i] == iteration)
                {
                    List<Tuple<Subplan, List<Subplan>, List<Constant>>> newvariants = GetNextSuitableTask(TaskTypeArray[i], -1, i, emptyVars, new List<Subplan>(new Subplan[TaskTypeArray.Length]), planSize, iteration); //Trying with emptz string with all vars it has error in fill maintask //Should this be new empty string or is allvars ok?
                    ruleVariants.AddRange(newvariants);
                }
            }
            List<RuleInstance> ruleInstances = new List<RuleInstance>();
            if (ruleVariants != null)
            {
                foreach (Tuple<Subplan, List<Subplan>, List<Constant>> ruleVariant in ruleVariants)
                {
                    if (ruleVariant.Item3.Contains(null)) //This might happen in multiple ways:
                                                          //1] main task has some parameter that none of its subtask look at. Problem one we fill by creating a task with all possible constants. 
                                                          //2] there is a forall condition in my conditions. This will not happen as in emptyvars this value is filled. 
                    {
                        List<List<Constant>> newAllVars = FillWithAllConstants(ruleVariant.Item3, AllVarsTypes, allConstants, new List<List<Constant>>());
                        newAllVars = newAllVars.Distinct().ToList();
                        foreach (List<Constant> allVar in newAllVars)
                        {
                            //Aside from making the rule instance we must also fill the main task properly here. 
                            Subplan t2 = FillMainTaskFromAllVars(allVar);
                            RuleInstance ruleInstance = new RuleInstance(t2, ruleVariant.Item2, this, allVar.Select(x => x.Name).ToList(), allConstants);
                            if (ruleInstance.IsValid())
                            {
                                ruleInstances.Add(ruleInstance);
                            }

                        }
                    }
                    else
                    {
                        RuleInstance ruleInstance = new RuleInstance(ruleVariant.Item1, ruleVariant.Item2, this, ruleVariant.Item3.Select(x => x.Name).ToList(), allConstants);
                        if (ruleInstance.IsValid()) ruleInstances.Add(ruleInstance);
                    }
                }
            }
            return ruleInstances;
        }

        /// <summary>
        /// Fills nulls in rule with all possible constants that fit the type. returns as one big list of list of strings. 
        /// changed publicity /// /// 
        /// </summary>
        /// <param name="item3"></param>
        /// <param name="allVarsTypes"></param>
        /// <param name="allConstants"></param>
        /// <returns></returns>
        internal List<List<Constant>> FillWithAllConstants(List<Constant> item3, List<ConstantType> allVarsTypes, List<Constant> allConstants, List<List<Constant>> solution)
        {
            int i = item3.IndexOf(null);
            if (i == -1)
            {
                solution.Add(item3);
                return solution;
            }
            else
            {
                ConstantType desiredType = AllVarsTypes[i];
                List<Constant> fittingConstants = allConstants.Where(x => desiredType.IsAncestorTo(x.Type)).ToList();
                foreach (Constant c in fittingConstants)
                {
                    List<Constant> newAllVars = new List<Constant>(item3);
                    newAllVars[i] = c;
                    List<List<Constant>> newSolutions = FillWithAllConstants(newAllVars, allVarsTypes, allConstants, solution);
                    solution.AddRange(newSolutions);
                    solution = solution.Distinct().ToList();
                    newAllVars = new List<Constant>(item3);
                }
                return solution;

            }
        }

        /// <summary>
        /// Creates empty vars from all vars. Empty vars is a list that is empty and as big as allvars but filled where rule uses constants not variable. 
        /// variables start with ?. 
        /// </summary>
        /// <returns></returns>
        private List<Constant> FillFromAllVars(List<Constant> allConstants)
        {
            List<Constant> emptyVars = new List<Constant>(new Constant[AllVars.Count]);
            for (int i = 0; i < AllVars.Count; i++)
            {
                if (!AllVars[i].StartsWith("?"))
                {
                    Constant c = allConstants.Where(x => x.Name == AllVars[i] && AllVarsTypes[i].IsAncestorTo(x.Type)).FirstOrDefault(); //If this is forall consatnt it will return null.
                    if (AllVars[i].StartsWith("!")) c = new Constant(AllVars[i], AllVarsTypes[i]);
                    emptyVars[i] = c;
                }
            }
            return emptyVars;
        }

        /// <summary>
        /// This finds all combinatiosn of subtasks for this rule. It finds them all at once. 
        /// </summary>
        /// <param name="t">Task type of main rule</param>
        /// <param name="index"> which subtask are we trying to fill now</param>
        /// <param name="newindex">index of the fixed new subtask we start with this one</param>
        /// <param name="partialAllVars">partially filled variables of the main rule</param>
        /// <param name="subtasks">partially filles list of subatssk of the main rule</param>
        /// <param name="planSize">total plan size</param>
        /// <param name="curIteration">current iteration</param>
        /// <returns>Returns list of tuples that contain main rule, filled subptasks and filled variables. </returns>
        private List<Tuple<Subplan, List<Subplan>, List<Constant>>> GetNextSuitableTask(TaskType t, int index, int newindex, List<Constant> partialAllVars, List<Subplan> subtasks, int planSize, int curIteration)
        {
            List<Subplan> unusedInstances = t.Instances.Except(subtasks).Distinct().ToList();
            if (index == -1) //Tasktype must be given as the new one. 
            {
                unusedInstances = unusedInstances.Where(x => x.Iteration == curIteration).ToList();
                index = newindex; //Temporarily we change the index so we don't have to change everything else and then after we switch it back to -1.

            }
            else if (index < newindex) //This ensures that if I have rule with 2 newsubtasks I wont get it twice. 
                                       //Anything after newindex can be both new and old. 
            {
                unusedInstances = unusedInstances.Where(x => x.Iteration < curIteration).ToList();
            }
            List<int> myReferences = ArrayOfReferenceLists[index];
            List<Tuple<Subplan, List<Subplan>, List<Constant>>> myResult = new List<Tuple<Subplan, List<Subplan>, List<Constant>>>();
            List<Tuple<Subplan, List<Subplan>, List<Constant>>> newMyResult = null;

            int oldIndex = 0; //Index of tasks already picked for this instance. 
            foreach (Subplan l in subtasks)
            {
                if (l != null)
                {
                    //These are tasks I already picked for this instance. 
                    if (IsBefore(index, oldIndex))
                    {
                        if (l.StartIndex == 0) unusedInstances = unusedInstances.Where(x => x.EndIndex <= l.StartIndex).ToList();  //For empty subatsks
                        else unusedInstances = unusedInstances.Where(x => x.EndIndex < l.StartIndex).ToList(); //Our task must be before this subtask so I shall only look at possible instances that end before the other starts. 
                    }
                    else if (IsBefore(oldIndex, index))
                    {
                        if (l.EndIndex == 0) unusedInstances = unusedInstances.Where(x => x.StartIndex >= l.EndIndex).ToList();
                        else unusedInstances = unusedInstances.Where(x => x.StartIndex > l.EndIndex).ToList(); //My task must start after task l.
                    }
                    unusedInstances = unusedInstances.Where(x => Differs(x.usedActions, l.usedActions)).ToList(); //NO problem with empty task becasue they return null.

                }
                oldIndex++;
            }

            if (numOfOrderedTasksAfterThisTask != null && numOfOrderedTasksAfterThisTask[index] > 0)
            {

                unusedInstances = unusedInstances.Where(x => x.EndIndex < planSize - minOrderedTaskPositionAfter[index]).ToList(); //assuming plan size of action number. So for plan from 0-7 plan size is 8.
            }
            if (numOfOrderedTasksBeforeThisTask != null && numOfOrderedTasksBeforeThisTask[index] > 0)
            {
                unusedInstances = unusedInstances.Where(x => x.StartIndex > minOrderedTaskPosition[index] - 1).ToList();
            }


            if (index == newindex) index = -1;
            foreach (Subplan tInstance in unusedInstances)
            {
                List<Constant> newAllVars = FillMainTask(tInstance, myReferences, partialAllVars);
                if (newAllVars == null) { }
                else
                {
                    List<Subplan> newSubTasks = new List<Subplan>(subtasks);
                    //The new subtask must be put in original order.
                    if (index == -1) newSubTasks[newindex] = tInstance;
                    else newSubTasks[index] = tInstance;
                    //We just assigned the last task. 
                    if (index == TaskTypeArray.Length - 1 || (index + 1 == newindex && newindex == TaskTypeArray.Length - 1))
                    {
                        if (myResult == null) myResult = new List<Tuple<Subplan, List<Subplan>, List<Constant>>>();
                        //We must fill up the main task from allVars.
                        Subplan newMainTask = FillMainTaskFromAllVars(newAllVars);
                        Tuple<Subplan, List<Subplan>, List<Constant>> thisTaskSubTaskCombo = Tuple.Create(newMainTask, newSubTasks, newAllVars);
                        myResult.Add(thisTaskSubTaskCombo);
                    }
                    else
                    {
                        if (index + 1 == newindex && newindex < TaskTypeArray.Length - 1)
                        {//This makes us skip the new task. because we already picked the task for the new task. 
                            newMyResult = GetNextSuitableTask(TaskTypeArray[index + 2], index + 2, newindex, newAllVars, newSubTasks, planSize, curIteration);
                        }
                        else
                        {
                            newMyResult = GetNextSuitableTask(TaskTypeArray[index + 1], index + 1, newindex, newAllVars, newSubTasks, planSize, curIteration);
                        }
                        myResult.AddRange(newMyResult);
                    }
                }

            }
            return myResult;
        }
        /// <summary>
        /// Returns true if arrays don't contain same elements. 
        /// </summary>
        /// <param name="usedActions1"></param>
        /// <param name="usedActions2"></param>
        /// <returns></returns>
        private bool Differs(bool[] usedActions1, bool[] usedActions2)
        {
            if (usedActions1 == null || !usedActions1.Any()) return true;
            if (usedActions2 == null || !usedActions2.Any()) return true;
            for (int i = 0; i < usedActions1.Length; i++)
            {
                if (i < usedActions2.Length && usedActions1[i] && usedActions2[i]) return false;
            }
            return true;
        }

        /// <summary>
        /// Returns true if task with index must be in rule before the task with oldindex.
        /// If there is no orderinng between them or if oldIndex task must be first we return false. 
        /// </summary>
        /// <param name="index"></param>
        /// <param name="oldIndex"></param>
        /// <returns></returns>
        private bool IsBefore(double index, double oldIndex)
        {
            if (orderConditions == null || !orderConditions.Any()) return false; //There is no ordering. 
            foreach (Tuple<int, int> tuple in orderConditions)
            {
                if (tuple.Item1 == index && tuple.Item2 == oldIndex) return true;
            }
            return false;
        }

        /// <summary>
        /// Fills the main task of a rule from the rule. 
        /// Here it's important that main task of a rule might have a lot less variables than he rule itself. 
        /// </summary>
        /// <param name="myAllVars"></param>
        /// <returns></returns>
        private Subplan FillMainTaskFromAllVars(List<Constant> myAllVars)
        {
            String taskName = MainTaskType.Name;
            Constant[] vars = new Constant[MainTaskReferences.Count];
            for (int i = 0; i < MainTaskReferences.Count; i++)
            {
                vars[i] = myAllVars[MainTaskReferences[i]];
            }
            Term term = new Term(taskName, vars);
            Subplan t = new Subplan(term, GetMin(TaskTypeActivationArray), GetMax(TaskTypeActivationArray), MainTaskType);
            return t;
        }
        /// <summary>
        /// Returns the index of the first true in the array. 
        /// </summary>
        /// <param name="array"></param>
        /// <returns></returns>
        private int GetMin(bool[] array)
        {
            for (int i = 0; i < array.Length; i++)
            {
                if (array[i]) return i;
            }
            return -1;
        }

        /// <summary>
        /// Returns the index of the last true in the array. 
        /// </summary>
        /// <param name="array"></param>
        /// <returns></returns>
        private int GetMax(bool[] array)
        {
            for (int i = array.Length - 1; i >= 0; i--)
            {
                if (array[i]) return i;
            }
            return -1;
        }

        /// <summary>
        /// Tries to fill the allvars in this rule. Currently will not fillthe main task variables those will be filled retrospectively if the rule filling is correct.
        /// Returns new string[] which represents new allVars adjusted. If it didn't work returns null.
        /// 
        /// </summary>
        /// <param name="t"></param>
        /// <param name="myReferences">references from subtasks to alvars</param>
        /// <param name="allVars">partially filled all vars</param>
        /// <returns></returns>
        private List<Constant> FillMainTask(Subplan t, List<int> myReferences, List<Constant> allVars)
        {
            List<Constant> newAllVars = new List<Constant>(allVars);
            for (int i = 0; i < myReferences.Count; i++)
            {
                //First check if the type fits adn then if so try to fill the avriable in. 
                ConstantType desiredType = AllVarsTypes[myReferences[i]];
                Constant myVariable = allVars[myReferences[i]];
                if (allVars[myReferences[i]] == null)
                {
                    //allvars is empty. Does what I want to put here fit my desired type if so I just add it if not I will return null.                     
                    if (desiredType.IsAncestorTo(t.TaskInstance.Variables[i].Type))
                    {
                        newAllVars[myReferences[i]] = t.TaskInstance.Variables[i];
                    }
                    else return null;
                }
                else if (t.TaskInstance.Variables[i].Name != myVariable.Name || !desiredType.IsAncestorTo(t.TaskInstance.Variables[i].Type)) //in all vars this variable is already assigned and its not to the same value as my variable. So this task cannot be used. 
                                                                                                                                             //we must also check if it's the right type. if not return null 
                {
                    return null;
                }
            }
            return newAllVars;
        }

        public override string ToString()
        {
            string text = "";
            if (TaskTypeArray != null && TaskTypeArray.Any()) text = string.Join(",", TaskTypeArray.Select(x => x.Name));
            string text2 = string.Join(",", AllVars);
            string text3 = string.Join(",", posPreConditions.Select(x => x.Item2)) + string.Join(",", posPreConditions.Select(x => x.Item3));
            string text4 = string.Join(",", negPreConditions.Select(x => x.Item2)) + string.Join(",", negPreConditions.Select(x => x.Item3));
            string text5 = string.Join(",", posPostConditions.Select(x => x.Item2)) + string.Join(",", posPostConditions.Select(x => x.Item3));
            string text6 = string.Join(",", negPostConditions.Select(x => x.Item2)) + string.Join(",", negPostConditions.Select(x => x.Item3));
            string text7 = string.Join(",", posBetweenConditions.Select(x => x.Item3)) + string.Join(",", posBetweenConditions.Select(x => x.Item4));
            string text8 = string.Join(",", negBetweenConditions.Select(x => x.Item3)) + string.Join(",", negBetweenConditions.Select(x => x.Item4));
            String s = "Rule " + Name + ": " + this.MainTaskType.Name + " subtasks " + text + " parameters " + text2 + " posPreCond" + text3 + "negPreCond " + text4 + "posPostCond " + text5 + " negPostCond " + text6 + "posBetweenCond " + text7 + "negBetweenCond" + text8;
            return s;
        }

    }
}
