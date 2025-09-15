using PlanRecognitionNETF;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Threading;

namespace PlanRecognitionExtension
{
    internal class EarleyParser : PlanRecognizerExtended, SuffixPruner 
    {
        public List<TaskType> AllTaskTypes { get; }
        public List<ActionType> AllActionTypes { get; }
        public List<Constant> AllConstants { get; }
        public List<ConstantType> AllConstantTypes { get; }
        static internal bool COMPUTING_SUPPORTS = false;
        public List<Subplan> PlanPrefix { get; set; }
        public List<Slot> PrefixTimeline { get; set; }
        public int CurrentParsingIteration { get; protected set; } // currently irrelevant
        public List<TaskType> AllDummyTaskTypes { get; protected set; }
        public List<Term> InitialState { get; private set; }
        public Slot DummyInitSlot { get; private set; }
        public int CurrentMaxAllowedCost { get; protected set; }
        public List<ActionSubplan> CurrentPlan { get; protected set; } = new();
        public List<Slot> CurrentTimeline { get; protected set; } = new();

        internal class ActionSubplan
        {
            public ActionSubplan(Subplan subplan, bool isInPlan, Action action)
            {
                Subplan = subplan;
                IsInPlan = isInPlan;
                Action = action;
            }

            internal Subplan Subplan { get; }
            internal bool IsInPlan { get; }
            internal Action Action { get; }
            internal List<Term> PosPreconditionsInheritedFromRules { get; } = new();
            internal List<Term> NegPreconditionsInheritedFromRules { get; } = new();

            public override string ToString()
            {
                return Subplan.ToString();
            }
        }

#if DEBUG
        static StreamWriter debugWriter = new StreamWriter("debug.txt")
        {
            AutoFlush = true
        };
        static StreamWriter debugWriter2 = new StreamWriter("debug_2.txt")
        {
            AutoFlush = true
        };
#endif

        public EarleyParser()
        { }

        public EarleyParser(List<TaskType> allTaskTypes, List<ActionType> allActionTypes, List<Constant> allConstants,
            List<ConstantType> allConstantTypes, List<Term> initialState)
        {
            AllTaskTypes = allTaskTypes;
            AllActionTypes = allActionTypes;
            AllConstants = allConstants;
            AllConstantTypes = allConstantTypes;
            InitialState = initialState;

            DummyInitSlot = new Slot(new Term("init_state", Array.Empty<Constant>()))
            {
                PosPostConditions = initialState
            };
        }

        internal abstract class CFGTask
        {
            internal abstract bool Subsumes(CFGTask cFGTask);
            internal abstract CFGTask Clone();
            public abstract override string ToString();
            internal abstract Constant[] GetConstants();
            internal abstract void SetVariable(int index, Constant value);

            internal void ResetVariable(int index)
            {
                SetVariableValue(index, null);
            }

            internal void SetVariableValue(int index, string value)
            {
                SetVariable(index, new(value, GetConstants()[index].Type));
            }

            protected List<Tuple<List<int>, Support>> thisTaskSupportsWithReferences = new List<Tuple<List<int>, Support>>();

            internal void AddSupportsFromSubtask(CFGTask subtask, List<int> thisTaskReferencesToRule, List<int> subtaskReferencesToRule)
            {

                foreach (var item in subtask.thisTaskSupportsWithReferences)
                {
                    List<int> supportReferencesToSubtask = item.Item1;
                    Support support = item.Item2;

                    List<int> supportReferencesToThisTask = new List<int>(supportReferencesToSubtask.Count);
                    foreach (int reference in supportReferencesToSubtask)
                    {
                        bool found = false;
                        if (reference >= 0)
                        {
                            int subtaskReferenceToRule = subtaskReferencesToRule[reference];
                            for (int i = 0; i < thisTaskReferencesToRule.Count; i++)
                            {
                                if (thisTaskReferencesToRule[i] == subtaskReferenceToRule)
                                {
                                    found = true;
                                    supportReferencesToThisTask.Add(i);
                                    break;
                                }
                            }
                        }
                        if (!found)
                        {
                            supportReferencesToThisTask.Add(-1);
                        }
                    }
                    thisTaskSupportsWithReferences.Add(new Tuple<List<int>, Support>(supportReferencesToThisTask, support));
                }
            }

            internal static bool SameTypeTasks(CFGTask task1, CFGTask task2)
            {
                if (task1 is AbstractTask abstractTask1 && task2 is AbstractTask abstractTask2)
                {
                    return abstractTask1.Task.TaskType.Equals(abstractTask2.Task.TaskType);
                }
                if (task1 is PrimitiveTask primitiveTask1 && task2 is PrimitiveTask primitiveTask2)
                {
                    return primitiveTask1.Action.ActionType.Equals(primitiveTask2.Action.ActionType);
                }
                return false;
            }

            protected bool FirstConstantArraySubsumesSecond(Constant[] first, Constant[] second) // arrays not null, same length
            {
                for (int i = 0; i < first.Length; i++)
                {
                    Constant constant1 = first[i];
                    Constant constant2 = second[i];
                    if (constant1 != null)
                    {
                        if (constant1.Name != null)
                        {
                            if (constant1.Name != constant2.Name)
                            {
                                return false;
                            }
                        }
                    }
                }
                return true;
            }

            public override abstract bool Equals(object obj);

            public override abstract int GetHashCode();

            internal void CloneSupportsFromOtherTask(AbstractTask otherTask)
            {
                Debug.Assert(thisTaskSupportsWithReferences.Count == 0);
                foreach (var item in otherTask.thisTaskSupportsWithReferences)
                {
                    thisTaskSupportsWithReferences.Add(new Tuple<List<int>, Support>(item.Item1, item.Item2.Clone()));
                }
            }

            internal void SetSupportVariables()
            {
                Constant[] instance = GetConstants();
                foreach (var item in thisTaskSupportsWithReferences)
                {
                    for (int i = 0; i < item.Item1.Count; i++)
                    {
                        int index = item.Item1[i];
                        if (index >= 0)
                        {
                            item.Item2.Action.SetVariable(i, instance[index]);
                        }
                    }
                }
            }

            protected bool SupportsEqual(CFGTask other)
            {
                return thisTaskSupportsWithReferences.Count == other.thisTaskSupportsWithReferences.Count &&
                    thisTaskSupportsWithReferences.ToHashSet(new SupportTupleComparer()).SetEquals(other.thisTaskSupportsWithReferences);
            }

            class SupportTupleComparer : IEqualityComparer<Tuple<List<int>, Support>>
            {
                public bool Equals(Tuple<List<int>, Support> x, Tuple<List<int>, Support> y)
                {
                    return x.Item2.Equals(y.Item2) && x.Item1.SequenceEqual(y.Item1);
                }

                public int GetHashCode(Tuple<List<int>, Support> obj)
                {
                    return obj.Item2.GetHashCode();
                }
            }
        }

        internal class AbstractTask : CFGTask
        {
            public AbstractTask(Task task)
            {
                Task = task;
            }

            internal Task Task { get; }

            public override bool Equals(object obj)
            {
                return obj != null && obj is AbstractTask task &&
                       Task.Equals(task.Task) && (!COMPUTING_SUPPORTS || SupportsEqual(task));
            }

            public override int GetHashCode()
            {
                return 658265964 + Task.GetHashCode();
            }

            public override string ToString()
            {
                return Task.ToString();
            }

            internal override CFGTask Clone()
            {
                Constant[] taskInstanceClone = new Constant[Task.TaskInstance.Length];
                for (int i = 0; i < taskInstanceClone.Length; i++)
                {
                    if (Task.TaskInstance[i] != null)
                    {
                        taskInstanceClone[i] = new Constant(Task.TaskInstance[i].Name, Task.TaskInstance[i].Type);
                    }
                }
                Task taskClone = new Task(Task.TaskType, taskInstanceClone);

                List<Tuple<List<int>, Support>> cloneSupports = new List<Tuple<List<int>, Support>>(thisTaskSupportsWithReferences.Count);
                foreach (var item in thisTaskSupportsWithReferences)
                {
                    cloneSupports.Add(new Tuple<List<int>, Support>(item.Item1, item.Item2.Clone()));
                }

                AbstractTask clone = new AbstractTask(taskClone);
                clone.thisTaskSupportsWithReferences = cloneSupports;
                return clone;
            }

            internal override Constant[] GetConstants()
            {
                return Task.TaskInstance;
            }

            internal override void SetVariable(int index, Constant value)
            {
                Task.SetVariable(index, value);
            }


            internal override bool Subsumes(CFGTask cFGTask)
            {
                if (cFGTask is AbstractTask abstractTask && abstractTask.Task.TaskType.Name == Task.TaskType.Name &&
                    abstractTask.Task.TaskType.NumOfVariables == Task.TaskType.NumOfVariables)
                {
                    return FirstConstantArraySubsumesSecond(Task.TaskInstance, abstractTask.Task.TaskInstance);
                }
                else
                {
                    return false;
                }
            }

            internal IEnumerable<Support> GetSupports()
            {
                List<Support> supports = new List<Support>(thisTaskSupportsWithReferences.Count);
                foreach (var item in thisTaskSupportsWithReferences)
                {
                    supports.Add(item.Item2);
                }
                return supports;
            }

            internal void ClearSupports()
            {
                thisTaskSupportsWithReferences = new List<Tuple<List<int>, Support>>();
            }
        }

        internal class PrimitiveTask : CFGTask
        {
            internal Action Action { get; }

            public PrimitiveTask(Action action)
            {
                Action = action;
            }

            internal override bool Subsumes(CFGTask cFGTask)
            {
                if (cFGTask is PrimitiveTask action && action.Action.ActionType.ActionTerm.Name == Action.ActionType.ActionTerm.Name &&
                    action.Action.ActionType.ActionTerm.Variables.Length == Action.ActionType.ActionTerm.Variables.Length)
                {
                    return FirstConstantArraySubsumesSecond(Action.ActionType.ActionTerm.Variables, action.Action.ActionType.ActionTerm.Variables);
                }
                else
                {
                    return false;
                }
            }

            internal override CFGTask Clone()
            {
                Constant[] actionInstanceClone = new Constant[Action.ActionInstance.Length];
                for (int i = 0; i < actionInstanceClone.Length; i++)
                {
                    if (Action.ActionInstance[i] != null)
                    {
                        actionInstanceClone[i] = new Constant(Action.ActionInstance[i].Name, Action.ActionInstance[i].Type);
                    }
                }
                Action actionClone = new Action(Action.ActionType, actionInstanceClone);
                return new PrimitiveTask(actionClone);
            }

            public override bool Equals(object obj)
            {
                return obj != null && obj is PrimitiveTask task &&
                       Action.Equals(task.Action) && (!COMPUTING_SUPPORTS || SupportsEqual(task));
            }

            public override int GetHashCode()
            {
                return -1969463049 + Action.GetHashCode();
            }

            public override string ToString()
            {
                return Action.ToString();
            }

            internal override Constant[] GetConstants()
            {
                return Action.ActionInstance;
            }

            internal override void SetVariable(int index, Constant value)
            {
                Action.SetVariable(index, value);
            }

            internal void AddSupportFromAction(Support support)
            {
                thisTaskSupportsWithReferences.Add(new Tuple<List<int>, Support>(Enumerable.Range(0, Action.ActionInstance.Length).ToList(),
                    support));
            }
        }

        internal class CFGRule
        {
            class LastState
            {
                public LastState(List<Constant> mainTaskInstantiation, List<List<Constant>> subtaskInstantiations)
                {
                    MainTaskInstantiation = mainTaskInstantiation;
                    SubtaskInstantiations = subtaskInstantiations;
                }

                internal List<Constant> MainTaskInstantiation { get; }
                internal List<List<Constant>> SubtaskInstantiations { get; }
            }

            public CFGRule(AbstractTask mainTask, CFGTask[] subtasks, Rule rule, EarleyParser parser)
            {
                MainTask = mainTask;
                Subtasks = subtasks;
                Rule = rule;

                SetSubtaskTypesFromRule(parser);
            }

            private void SetSubtaskTypesFromRule(EarleyParser parser)
            {
                if (!IsDummyRule(parser))
                {
                    for (int i = 0; i < MainTask.Task.TaskType.NumOfVariables; i++)
                    {
                        if (Rule.AllVarsTypes.Count > 0 && Rule.MainTaskReferences[i] >= 0 &&
                            !MainTask.Task.TaskInstance[i].Type.Equals(Rule.AllVarsTypes[Rule.MainTaskReferences[i]])
                            && MainTask.Task.TaskInstance[i].Type.IsAncestorTo(Rule.AllVarsTypes[Rule.MainTaskReferences[i]]))
                        {
                            MainTask.SetVariable(i, new Constant(MainTask.Task.TaskInstance[i].Name,
                                Rule.AllVarsTypes[Rule.MainTaskReferences[i]]));
                        }
                    }

                    for (int j = 0; j < Subtasks.Length; j++)
                    {
                        for (int i = 0; i < Subtasks[j].GetConstants().Length; i++)
                        {
                            if (Rule.AllVarsTypes.Count > 0
                                && !Subtasks[j].GetConstants()[i].Type.Equals(Rule.AllVarsTypes[Rule.ArrayOfReferenceLists[j][i]])
                                && Subtasks[j].GetConstants()[i].Type.IsAncestorTo(Rule.AllVarsTypes[Rule.ArrayOfReferenceLists[j][i]]))
                            {
                                Subtasks[j].SetVariable(i, new Constant(Subtasks[j].GetConstants()[i].Name,
                                    Rule.AllVarsTypes[Rule.ArrayOfReferenceLists[j][i]]));
                            }
                        }
                    }
                }
            }

            public CFGRule(AbstractTask mainTask, CFGTask[] subtasks, int currentSubtaskIndex, Rule rule, EarleyParser parser)
                : this(mainTask, subtasks, rule, parser)
            {
                CurrentSubtaskIndex = currentSubtaskIndex;
            }

            public AbstractTask MainTask { get; }
            public CFGTask[] Subtasks { get; }
            public int CurrentSubtaskIndex { get; private set; }
            public Rule Rule { get; }

            readonly Stack<LastState> lastStateStack = new();

            internal bool IsEmptyRule => !(Subtasks.Length > 0);

            internal bool SetVariablesFromMainTask(CFGTask cFGTask)
            {
                SaveCurrentState();

                var cFGTaskConstants = cFGTask.GetConstants();
                var currentMainTaskConstants = MainTask.GetConstants();

                for (int mainTaskVarIndex = 0; mainTaskVarIndex < cFGTaskConstants.Length; mainTaskVarIndex++)
                {
                    if (!(currentMainTaskConstants[mainTaskVarIndex]?.Name?.Length > 0))
                    {
                        MainTask.SetVariable(mainTaskVarIndex, cFGTaskConstants[mainTaskVarIndex]);
                    }
                }

                for (int subtaskIndex = 0; subtaskIndex < Subtasks.Length; subtaskIndex++)
                {
                    var currentSubtaskConstants = Subtasks[subtaskIndex].GetConstants();

                    for (int subtaskVarIndex = 0; subtaskVarIndex < Rule.ArrayOfReferenceLists[subtaskIndex].Count; subtaskVarIndex++)
                    {
                        int subtaskVar = Rule.ArrayOfReferenceLists[subtaskIndex][subtaskVarIndex];
                        for (int mainTaskVarIndex = 0; mainTaskVarIndex < cFGTaskConstants.Length; mainTaskVarIndex++)
                        {
                            int mainTaskVar = Rule.MainTaskReferences[mainTaskVarIndex];
                            if (subtaskVar == mainTaskVar)
                            {
                                if (!(currentSubtaskConstants[subtaskVarIndex]?.Name?.Length > 0))
                                {
                                    Subtasks[subtaskIndex].SetVariable(subtaskVarIndex, cFGTaskConstants[mainTaskVarIndex]);
                                }
                                else if (currentSubtaskConstants[subtaskVarIndex]?.Name?.Length > 0 && cFGTaskConstants[mainTaskVarIndex]?.Name?.Length > 0 &&
                                    currentSubtaskConstants[subtaskVarIndex].Name != cFGTaskConstants[mainTaskVarIndex].Name)
                                {
                                    return false;
                                }
                            }
                        }
                    }
                }

                return true;
            }

            private void SaveCurrentState()
            {
                List<Constant> mainTaskConstants = MainTask.GetConstants().ToList();
                List<List<Constant>> subtaskConstants = new();
                for (int i = 0; i < Subtasks.Length; i++)
                {
                    subtaskConstants.Add(Subtasks[i].GetConstants().ToList());
                }

                lastStateStack.Push(new LastState(mainTaskConstants, subtaskConstants));
            }

            internal void ResetVariables()
            {
                if (lastStateStack.Count == 0)
                {
                    throw new InvalidOperationException("Last state not set.");
                }

                var lastState = lastStateStack.Pop();

                for (int i = 0; i < lastState.MainTaskInstantiation.Count; i++)
                {
                    MainTask.SetVariable(i, lastState.MainTaskInstantiation[i]);
                }

                for (int i = 0; i < lastState.SubtaskInstantiations.Count; i++)
                {
                    for (int j = 0; j < lastState.SubtaskInstantiations[i].Count; j++)
                    {
                        Subtasks[i].SetVariable(j, lastState.SubtaskInstantiations[i][j]);
                    }
                }
            }

            internal CFGRule Clone(EarleyParser parser)
            {
                CFGTask[] subtasksClone = new CFGTask[Subtasks.Length];
                for (int i = 0; i < Subtasks.Length; i++)
                {
                    subtasksClone[i] = Subtasks[i].Clone();
                }
                CFGRule newCFGRule = new CFGRule(MainTask.Clone() as AbstractTask, subtasksClone, Rule, parser);
                newCFGRule.CurrentSubtaskIndex = CurrentSubtaskIndex;
                return newCFGRule;
            }

            public void IncrementCurrentSubtaskIndex()
            {
                ++CurrentSubtaskIndex;
            }

            internal bool Finished()
            {
                return CurrentSubtaskIndex == Subtasks.Length;
            }

            internal bool TryGetNextTask(out CFGTask nextTask)
            {
                if (!Finished() && CurrentSubtaskIndex < Subtasks.Length)
                {
                    nextTask = Subtasks[CurrentSubtaskIndex];
                    return true;
                }
                else
                {
                    nextTask = null;
                    return false;
                }
            }

            internal CFGTask GetLastTask()
            {
                return Subtasks[Subtasks.Length - 1];
            }

            public override bool Equals(object obj)
            {
                return obj != null && obj is CFGRule rule &&
                    CurrentSubtaskIndex == rule.CurrentSubtaskIndex &&
                    MainTask.Task.Equals(rule.MainTask.Task) && // supports of the main task are not needed for comparison - they are computed from supports of subtasks
                    Enumerable.SequenceEqual(Subtasks, rule.Subtasks);
            }

            public override int GetHashCode()
            {
                int hashCode = 1302199088;
                hashCode = hashCode * -1521134295 + MainTask.GetHashCode(); EqualityComparer<AbstractTask>.Default.GetHashCode(MainTask);
                foreach (var task in Subtasks)
                {
                    hashCode = hashCode * -1521134295 + task.GetHashCode();
                }
                hashCode = hashCode * -1521134295 + CurrentSubtaskIndex;
                return hashCode;
            }

            public override string ToString()
            {
                string s = MainTask.ToString() + " → ";
                for (int i = 0; i < Subtasks.Length; i++)
                {
                    CFGTask task = Subtasks[i];
                    if (i > 0)
                    {
                        s += ", ";
                    }
                    if (CurrentSubtaskIndex == i)
                    {
                        s += "#";
                    }
                    s += task.ToString();
                }
                if (CurrentSubtaskIndex == Subtasks.Length)
                {
                    s += "#";
                }
                return s;
            }

            internal void MoveSupportsToMainTask()
            {
                for (int i = 0; i < Subtasks.Length; i++)
                {
                    CFGTask task = Subtasks[i];
                    MainTask.AddSupportsFromSubtask(task, Rule.MainTaskReferences, Rule.ArrayOfReferenceLists[i]);
                }
            }

            internal IEnumerable<Support> GetSupports()
            {
                MoveSupportsToMainTask();
                return MainTask.GetSupports();
            }

            internal IEnumerable<Subplan> GetGroundedSubplans(EarleyParser parser, 
                IGroundable correspondingQueueItem, int startIndex,
                IEnumerable<IGroundable>[] SubtaskCompletingRules, int maxAllowedCost, int currentCost,
                Slot lastSlot, double lastEndIndex, CancellationToken cancellationToken, 
                int groundingDepth = -1)
            {
#if DEBUG
                //Console.WriteLine($"grounding depth: {groundingDepth}");
                //for (int i = 0; i < groundingDepth; i++)
                //{
                //    Console.Write(' ');

                //}
#endif
                if (IsLeaf())
                {
                    return GetLeafSubplans(parser, startIndex, correspondingQueueItem.IsActionInPrefix(parser), cancellationToken);
                }
                else
                {
                    return GetInternalNodeSubplans(parser, startIndex, SubtaskCompletingRules, maxAllowedCost, currentCost, lastSlot, lastEndIndex,
                        cancellationToken);
                }
            }

            bool IsConstantInstantiated(Constant var)
            {
                return var?.Name?.Length > 0;
            }

            bool IsInequalityPreconditionViolated(List<string> ruleVariables, Tuple<int, string, List<int>> ineqPrecond, List<Subplan> groundedSubtasks)
            {
                var variables = InstantiateConditionFromMainTaskAndSubtasks(ineqPrecond, groundedSubtasks, ruleVariables);

                for (int i = 0; i < variables.Length; i++)
                {
                    for (int j = 0; j < variables.Length; j++)
                    {
                        if (i != j && IsConstantInstantiated(variables[i]) && IsConstantInstantiated(variables[j]) && variables[i].Equals(variables[j]))
                        {
                            return true;
                        }
                    }
                }

                return false;
            }

            private bool InstantiateMainTaskAndSubtasksFromEqualityPreconditions(List<Tuple<int, int>> changedSubtasksVariables, List<int> changedMainTaskVariables, List<Subplan> groundedSubtasks, EarleyParser parser)
            {
                if (IsDummyRule(parser))
                {
                    return true;
                }

                var ruleVariables = GetRuleVariables();

                foreach (var posPrecond in Rule.posPreConditions)
                {
                    if (IsEqualityCondition(posPrecond))
                    {
                        var variables = InstantiateConditionFromMainTaskAndSubtasks(posPrecond, groundedSubtasks, ruleVariables);

                        if (!InstantiateMainTaskAndSubtasksFromEqualityPrecondition(ruleVariables, posPrecond, variables, changedSubtasksVariables, changedMainTaskVariables, groundedSubtasks))
                        {
                            return false;
                        }
                    }
                }

                return true;
            }

            private bool InstantiateMainTaskAndSubtasksFromEqualityPrecondition(List<string> ruleVariables, Tuple<int, string, List<int>> posPrecond, Constant[] variables,
                List<Tuple<int, int>> changedSubtasksVariables, List<int> changedMainTaskVariables, List<Subplan> groundedSubtasks)
            {
                for (int i = 0; i < variables.Length; i++)
                {
                    Constant var = variables[i];
                    for (int j = 0; j < variables.Length; j++)
                    {
                        if (i != j)
                        {
                            if (var?.Name?.Length > 0)
                            {
                                if (variables[j]?.Name?.Length > 0)
                                {
                                    if (!var.Equals(variables[j]))
                                    {
                                        return false;
                                    }
                                }
                                else
                                {
                                    // main task:
                                    for (int mainTaskVarIndex = 0; mainTaskVarIndex < Rule.MainTaskReferences.Count; mainTaskVarIndex++)
                                    {
                                        int reference = Rule.MainTaskReferences[mainTaskVarIndex];
                                        if (reference == posPrecond.Item3[i])
                                        {
                                            if (MainTask.GetConstants()[mainTaskVarIndex]?.Name?.Length == 0)
                                            {
                                                MainTask.SetVariable(mainTaskVarIndex, var);
                                                changedMainTaskVariables.Add(mainTaskVarIndex);
                                            }
                                            else if (!MainTask.GetConstants()[mainTaskVarIndex].Equals(var))
                                            {
                                                return false;
                                            }
                                        }
                                    }
                                    // subtasks:
                                    for (int subtaskIndex = 0; subtaskIndex < Rule.ArrayOfReferenceLists.Length; subtaskIndex++)
                                    {
                                        List<int> subtaskReferences = Rule.ArrayOfReferenceLists[subtaskIndex];
                                        for (int subtaskVarIndex = 0; subtaskVarIndex < subtaskReferences.Count; subtaskVarIndex++)
                                        {
                                            int reference = subtaskReferences[subtaskVarIndex];
                                            if (reference == posPrecond.Item3[i])
                                            {
                                                if (Subtasks[subtaskIndex].GetConstants()[subtaskIndex]?.Name?.Length == 0)
                                                {
                                                    Subtasks[subtaskIndex].SetVariable(subtaskVarIndex, var);
                                                    changedSubtasksVariables.Add(new(subtaskIndex, subtaskVarIndex));
                                                }
                                                else if (!Subtasks[subtaskIndex].GetConstants()[subtaskIndex].Equals(var))
                                                {
                                                    return false;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }

                return true;
            }

            internal bool IsAnyInequalityPreconditionViolated(List<Subplan> groundedSubtasks, EarleyParser parser)
            {
                if (IsDummyRule(parser))
                {
                    return false;  // there are no preconditions and variables are not set in dummy starting rules
                }

                var ruleVariables = GetRuleVariables();

                foreach (var negPrecond in Rule.negPreConditions)
                {
                    if (IsEqualityCondition(negPrecond) && IsInequalityPreconditionViolated(ruleVariables, negPrecond, groundedSubtasks))
                    {
                        return true;
                    }
                }

                return false;
            }

            bool IsPreconditionGrounded(Constant[] variables)
            {
                foreach (var v in variables)
                {
                    if (v == null || v.Name == null || v.Name.Length == 0)
                    {
                        return false;
                    }
                }

                return true;
            }

            Constant[] InstantiateConditionFromMainTask(Tuple<int, string, List<int>> precond, List<string> ruleVariables)
            {
                Constant[] variables = new Constant[precond.Item3.Count];

                for (int i = 0; i < precond.Item3.Count; i++)
                {
                    variables[i] = new Constant(ruleVariables[precond.Item3[i]], Rule.AllVarsTypes[precond.Item3[i]]);
                }

                return variables;
            }

            List<string> FillRuleVariablesFromSubtasks(List<Subplan> groundedSubtasks, List<string> ruleVariables)
            {
                var result = new List<string>(ruleVariables);

                for (int i = 0; i < groundedSubtasks.Count; i++)
                {
                    List<int> subtaskReferences = Rule.ArrayOfReferenceLists[i];
                    for (int j = 0; j < subtaskReferences.Count; j++)
                    {
                        result[subtaskReferences[j]] = groundedSubtasks[i].TaskInstance.Variables[j]?.Name;
                    }
                }
                return result;
            }

            Constant[] InstantiateConditionFromMainTaskAndSubtasks(Tuple<int, string, List<int>> precond, List<Subplan> groundedSubtasks, List<string> ruleVariables)
            {
                var newRuleVariables = FillRuleVariablesFromSubtasks(groundedSubtasks, ruleVariables);
                var variables = InstantiateConditionFromMainTask(precond, newRuleVariables);
                return variables;
            }

            bool IsPositivePreconditionViolated(List<string> ruleVariables, Tuple<int, string, List<int>> posPrecond, Slot previousSlot)
            {
                return IsPreconditionViolated(ruleVariables, posPrecond, previousSlot, true);
            }

            bool IsNegativePreconditionViolated(List<string> ruleVariables, Tuple<int, string, List<int>> negPrecond, Slot previousSlot)
            {
                return IsPreconditionViolated(ruleVariables, negPrecond, previousSlot, false);
            }

            bool IsPreconditionViolated(List<string> ruleVariables, Tuple<int, string, List<int>> precond, Slot previousSlot, bool preconditionIsPositive)
            {
                Constant[] variables = InstantiateConditionFromMainTask(precond, ruleVariables);

                if (!IsPreconditionGrounded(variables))
                {
                    return false;
                }

                Term precondTerm = new(precond.Item2, variables);

                if (preconditionIsPositive)
                {
                    return !previousSlot.PosPostConditions.Contains(precondTerm);
                }
                else
                {
                    return previousSlot.PosPostConditions.Contains(precondTerm);
                }
            }

            List<string> GetRuleVariables()
            {
                List<string> result = Enumerable.Repeat("", Rule.AllVarsTypes.Count).ToList();

                Constant[] mainTaskVariables = MainTask.GetConstants();
                for (int i = 0; i < mainTaskVariables.Length; i++)
                {
                    Constant variable = mainTaskVariables[i];
                    result[Rule.MainTaskReferences[i]] = variable?.Name;
                }

                for (int i = 0; i < Rule.ArrayOfReferenceLists.Length; i++)
                {
                    List<int> subtaskReferences = Rule.ArrayOfReferenceLists[i];
                    for (int j = 0; j < subtaskReferences.Count; j++)
                    {
                        result[subtaskReferences[j]] = Subtasks[i].GetConstants()[j]?.Name;
                    }
                }

                return result;
            }

            static bool IsEqualityCondition(Tuple<int, string, List<int>> precond)
            {
                return precond.Item2.Contains("equal") || precond.Item2.Equals("=");
            }

            static bool IsPreconditionOfWholeRule(Tuple<int, string, List<int>> precond)
            {
                return precond.Item1 == -1 || precond.Item1 == 0;
            }

            internal bool CheckEmptyRuleConstraints(Slot relevantSlot)
            {
                return !IsAnyNonEqualityRulePreconditionViolated(relevantSlot);
            }

            internal bool IsAnyNonEqualityRulePreconditionViolated(Slot previousSlot)
            {
                var ruleVariables = GetRuleVariables();

                foreach (var posPrecond in Rule.posPreConditions)
                {
                    if (!IsEqualityCondition(posPrecond) && IsPreconditionOfWholeRule(posPrecond) && IsPositivePreconditionViolated(ruleVariables, posPrecond, previousSlot))
                    {
                        return true;
                    }
                }

                foreach (var negPrecond in Rule.negPreConditions)
                {
                    if (!IsEqualityCondition(negPrecond) && IsPreconditionOfWholeRule(negPrecond) && IsNegativePreconditionViolated(ruleVariables, negPrecond, previousSlot))
                    {
                        return true;
                    }
                }

                return false;
            } 

            internal bool IsDummyRule(EarleyParser parser)
            {
                return parser.AllDummyTaskTypes.Contains(MainTask.Task.TaskType);
            }

            IEnumerable<Subplan> GetInternalNodeSubplans(EarleyParser parser, int startIndex,
                IEnumerable<IGroundable>[] subtaskCompletingRules, int maxAllowedCost, int currentCost,
Slot lastSlot, double lastEndIndex, CancellationToken cancellationToken)
            {

                SetVariablesFromConstants(parser);

                foreach (var groundedSubtasks in
                    GetGroundedSubtasks(parser, startIndex, subtaskCompletingRules,
                    maxAllowedCost, currentCost, lastSlot, lastEndIndex,
                    cancellationToken))
                {
                    if (cancellationToken.IsCancellationRequested)
                    {
                        yield break;
                    }

                    if (IsDummyRule(parser))
                    {
                        if (parser.CheckWholeTimeline(out var newCurrentPlan)) // necessary for TIHTN planner
                        { 
                            var oldCurrentPlan = parser.CurrentPlan;
                            parser.CurrentPlan = newCurrentPlan;

                            yield return parser.GoalTask(groundedSubtasks);
                            parser.CurrentPlan = oldCurrentPlan;
                        }
                    }

                    else
                    {
                        foreach (RuleInstance ruleInstance in 
                            GroundRuleFromSubtasksAndMainTask(groundedSubtasks, parser))
                        {
                            if (ValidVarTypes(ruleInstance, parser))
                            {
                                var redistributedSubtasks = parser.RedistributeSubtasks(groundedSubtasks);
                                Subplan subplan = parser.MergePlans(redistributedSubtasks, 
                                    ruleInstance.MainTask.TaskInstance,
                                    MainTask.Task.TaskType, parser.PrefixTimeline);

                                if (parser.PrefixTimeline.Count == 1) // for partial observability
                                                                      
                                {
                                    AddInitStateConditions(subplan, parser);
                                }

                                if (subplan != null)
                                {
                                    subplan.Iteration = parser.CurrentParsingIteration;


                                    if (parser.RulePreconditionsSatisfied(subplan, ruleInstance,
                                        startIndex,
                                        groundedSubtasks, out _, out _, out var actionsToInsert,
                                        out var correspondingActions))
                                    {     
                                        if (actionsToInsert.Count > 0)
                                        {
                                            parser.AddToCurrentPlan(ruleInstance.FirstIndexInCurrentPlan,
                                                actionsToInsert.Zip(correspondingActions,
                                                (x, y) => new ActionSubplan(x, false, y)).ToArray());
                                            List<Term> lastSlotConditions = 
                                                parser.GetLastSlotConditions(
                                                    ruleInstance.FirstIndexInCurrentPlan
                                                    + actionsToInsert.Count);
                                            Slot lastSlotFromConditions = new Slot();
                                            lastSlotFromConditions.PosPostConditions = lastSlotConditions;
                                            subplan.Timeline = PropagateTimeline(lastSlotFromConditions, 
                                                subplan.Timeline);
                                        }
                                        if (parser.ApplyConditionsAndCheckValidity(subplan, ruleInstance, 
                                            groundedSubtasks, parser))
                                        {
                                            subplan.AddToHistory(ruleInstance);

                                            yield return subplan;
                                            parser.RemoveFromCurrentPlan(ruleInstance.FirstIndexInCurrentPlan, actionsToInsert.Count);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }

            internal void SetVariablesFromConstants(EarleyParser parser)
            {
                if (IsDummyRule(parser))
                {
                    return;
                }

                var mainTaskConstants = MainTask.GetConstants();
                for (int i = 0; i < Rule.MainTaskReferences.Count; i++)
                {
                    if (!IsConstantInstantiated(mainTaskConstants[i]))
                    {
                        var constantVar = Rule.AllVars[Rule.MainTaskReferences[i]];
                        if (constantVar?.Length > 0 && !constantVar.StartsWith('?'))
                        {
                            MainTask.SetVariable(i, new Constant(constantVar, mainTaskConstants[i].Type));
                        }
                    }
                }

                for (int subtask = 0; subtask < Subtasks.Length; subtask++)
                {
                    var subtaskConstants = Subtasks[subtask].GetConstants();
                    for (int i = 0; i < Rule.ArrayOfReferenceLists[subtask].Count; i++)
                    {
                        if (!IsConstantInstantiated(subtaskConstants[i]))
                        {
                            var constantVar = Rule.AllVars[Rule.ArrayOfReferenceLists[subtask][i]];
                            if (constantVar?.Length > 0 && !constantVar.StartsWith('?'))
                            {
                                Subtasks[subtask].SetVariable(i, new Constant(constantVar, subtaskConstants[i].Type));
                            }
                        }
                    }
                }
            }

            private static void AddInitStateConditions(Subplan subplan, EarleyParser parser) 
            {
                subplan.GetSlot(0).PosPreConditions = UnifyConditions(subplan.GetSlot(0).PosPreConditions, parser.InitialState);
                List<Term> c1 = RemoveConditions(subplan.GetSlot(0).PosPreConditions, subplan.GetSlot(0).NegPostConditions);
                subplan.GetSlot(0).PosPostConditions = UnifyConditions(subplan.GetSlot(0).PosPostConditions, c1);
            }

            IEnumerable<RuleInstance> GroundRuleFromSubtasksAndMainTask(List<Subplan> groundedSubtasks, EarleyParser parser)
            {

                List<string> allVars = Enumerable.Repeat<string>(null, Rule.AllVars.Count).ToList();
                for (int i = 0; i < groundedSubtasks.Count; i++)
                {
                    Subplan subtask = groundedSubtasks[i];
                    List<int> varReferences = Rule.ArrayOfReferenceLists[i];
                    for (int j = 0; j < varReferences.Count; j++)
                    {
                        string var = subtask.TaskInstance.Variables[j].Name;
                        int allVarsIndex = varReferences[j];

                        if (var != null)
                        {
                            if (allVars[allVarsIndex] != null && allVars[allVarsIndex] != var)
                            {
                                yield break;
                            }
                            allVars[allVarsIndex] = var;
                        }
                    }
                }

                for (int i = 0; i < Rule.MainTaskReferences.Count; i++)
                {
                    string var = MainTask.GetConstants()[i].Name;
                    int allVarsIndex = Rule.MainTaskReferences[i];

                    if (var != null)
                    {
                        if (allVars[allVarsIndex] != null && allVars[allVarsIndex] != var)
                        {
                            yield break;
                        }
                        allVars[allVarsIndex] = var;
                    }
                }

                GroundVarsFromConstantEquality(allVars);
                foreach (var grounding in GroundUngroundedVariables(allVars, Rule.AllVarsTypes))
                {
                    Subplan mainTask = GroundMainTask(allVars);
                    yield return new RuleInstance(mainTask, groundedSubtasks, Rule, grounding, parser.AllConstants);
                }


            }

            private void GroundVarsFromConstantEquality(List<string> allVars)
            {
                for (int i = 0; i < Rule.AllVars.Count; i++)
                {
                    string var = Rule.AllVars[i];
                    if (!var.StartsWith("?"))
                    {
                        allVars[i] = var;
                    }
                }
            }

            internal static IEnumerable<List<string>> GroundUngroundedVariables(List<string> allVars, List<ConstantType> allVarsTypes)
            {
                return GroundUngroundedVariables(allVars, allVarsTypes, 0);
            }

            internal static IEnumerable<List<string>> GroundUngroundedVariables(List<string> allVars, List<ConstantType> types, 
                int indexToGround) 
            {
                if (indexToGround == allVars.Count)
                {
                    yield return allVars;
                }
                else
                {
                    if (allVars[indexToGround] != null)
                    {
                        foreach (var grounding in GroundUngroundedVariables(allVars, types, indexToGround + 1))
                        {
                            yield return grounding;
                        }
                    }
                    else
                    {
                        foreach (var descendantType in types[indexToGround].DescendantTypes)
                        {
                            foreach (var value in descendantType.Instances)
                            {
                                allVars[indexToGround] = value.Name;
                                foreach (var grounding in GroundUngroundedVariables(allVars, types, indexToGround + 1))
                                {
                                    yield return grounding;
                                }
                                allVars[indexToGround] = null;
                            }
                        }
                    }
                }
            }


            private Subplan GroundMainTask(List<string> allVars)
            {
                Constant[] vars = new Constant[Rule.MainTaskReferences.Count];
                for (int i = 0; i < Rule.MainTaskReferences.Count; i++)
                {
                    vars[i] = new Constant(allVars[Rule.MainTaskReferences[i]], Rule.AllVarsTypes[Rule.MainTaskReferences[i]]);
                }
                Term term = new Term(Rule.MainTaskType.Name, vars);
                Subplan t = new Subplan(term, 0, Subtasks.Length - 1, MainTask.Task.TaskType);
                return t;
            }

            internal static bool ApplyConditionsAndCheckValidity(Subplan subplan, 
                RuleInstance ruleInstance, 
                List<Subplan> subtasks, EarleyParser parser, 
                int indexToCheckPreconditionsFrom = 0 /*important for TIHTN**/)
            {
                if (!ApplyPre(subplan.Timeline.GetRange(indexToCheckPreconditionsFrom, 
                    subplan.Timeline.Count - indexToCheckPreconditionsFrom), 
                    ruleInstance.PosPreConditions, ruleInstance.NegPreConditions, 
                    (int)subplan.StartIndex,
                    parser.PrefixTimeline.Count))
                {
                    return false;
                }

                parser.ApplyPost(subplan.Timeline, ruleInstance.PosPostConditions, ruleInstance.NegPostConditions);

                if (!parser.ApplyBetween(subplan.Timeline, ruleInstance.PosBetweenConditions, ruleInstance.NegBetweenConditions, (int)Math.Ceiling(subplan.StartIndex), parser.PrefixTimeline.Count))
                {
                    return false;
                }

                if (subplan.EndIndex >= parser.PrefixTimeline.Count)
                {
                    if (!parser.MegaslotPropagate(ref subplan.Timeline, parser.PrefixTimeline.Count, 
                        (int)Math.Ceiling(subplan.StartIndex)))
                    {
                        return false;
                    }
                }

                if (!parser.CheckValidity(subplan.Timeline))
                {
                    return false;
                }

                subplan.CreateUsedActions(subtasks);
                return true;
            }

            private IEnumerable<List<Subplan>> GetGroundedSubtasks(EarleyParser pruner, int startIndex,
                IEnumerable<IGroundable>[] subtaskCompletingRules, int maxAllowedCost, int currentCost,
                Slot lastSlot,
                double lastEndIndex,
                CancellationToken cancellationToken)
            {
                return GetGroundedSubtasks(new List<Subplan>(), 0, pruner, startIndex, subtaskCompletingRules, cancellationToken,
                    maxAllowedCost, currentCost, lastSlot, lastEndIndex);
            }

            // Left-to-right propagation. Preconditions are expected to be satisfied.
            // For total order - expects non-empty slots.
            // Returns the last slot.
            internal static Slot Propagate(Slot lastSlot, List<Slot> timeline)
            {
                return PropagateTimeline(lastSlot, timeline).Last();
            }

            internal static List<Slot> PropagateTimeline(Slot lastSlot, List<Slot> timeline)
            {
                List<Slot> modifiedTimeline = new List<Slot>
                {
                    lastSlot
                };

                foreach (var slot in timeline)
                {
                    modifiedTimeline.Add(new Slot(slot));
                }

                foreach (var s in modifiedTimeline)
                {
                    s.PosPreConditions ??= new();
                    s.PosPostConditions ??= new();
                    s.NegPreConditions ??= new();
                    s.NegPostConditions ??= new();
                }

                for (int i = 1; i < modifiedTimeline.Count; i++)
                {
                    modifiedTimeline[i].PosPreConditions.AddRange(modifiedTimeline[i - 1].PosPostConditions);
                    modifiedTimeline[i].NegPreConditions.AddRange(modifiedTimeline[i - 1].NegPostConditions);
                    modifiedTimeline[i].PosPreConditions = modifiedTimeline[i].PosPreConditions.Distinct().ToList();
                    modifiedTimeline[i].NegPreConditions = modifiedTimeline[i].NegPreConditions.Distinct().ToList();

                    modifiedTimeline[i].PosPostConditions.AddRange(modifiedTimeline[i].PosPreConditions.Where(
                        x => !modifiedTimeline[i].NegPostConditions.Contains(x)));
                    modifiedTimeline[i].NegPostConditions.AddRange(modifiedTimeline[i].NegPreConditions.Where(
                        x => !modifiedTimeline[i].PosPostConditions.Contains(x)));

                    modifiedTimeline[i].PosPostConditions = modifiedTimeline[i].PosPostConditions.Distinct().ToList();
                    modifiedTimeline[i].NegPostConditions = modifiedTimeline[i].NegPostConditions.Distinct().ToList();

                    modifiedTimeline[i].NegPostConditions.RemoveAll(x => modifiedTimeline[i].PosPostConditions.Contains(x));
                }

                return modifiedTimeline.GetRange(1, modifiedTimeline.Count - 1);
            }

            IEnumerable<List<Subplan>> GetGroundedSubtasks(List<Subplan> groundedSubtasks, int subtaskToGround, EarleyParser parser,
                int startIndex, IEnumerable<IGroundable>[] subtaskCompletingRules, CancellationToken cancellationToken,
                int maxAllowedCost, int currentCost, Slot lastSlot, double lastEndIndex)
            {
                if (IsAnyInequalityPreconditionViolated(groundedSubtasks, parser))
                {
                    yield break;
                }
                if (currentCost > maxAllowedCost)
                {
                    yield break;
                }
                if (subtaskToGround == Subtasks.Length)
                {
                    yield return groundedSubtasks;
                }
                else
                {
                    List<int> changedVariables = new List<int>();
                    List<Tuple<int, int>> changedSubtaskVariables = new();

                    for (int i = 0; i < groundedSubtasks.Count; i++)
                    {
                        for (int j = 0; j < Rule.ArrayOfReferenceLists[i].Count; j++)
                        {
                            for (int k = 0; k < Rule.ArrayOfReferenceLists[subtaskToGround].Count; k++)
                            {
                                if (Rule.ArrayOfReferenceLists[i][j] == Rule.ArrayOfReferenceLists[subtaskToGround][k])
                                {
                                    if (Subtasks[subtaskToGround].GetConstants()[k] == null
                                        || Subtasks[subtaskToGround].GetConstants()[k].Name == null
                                        || Subtasks[subtaskToGround].GetConstants()[k].Name == "")
                                    {
                                        Subtasks[subtaskToGround].SetVariable(k, groundedSubtasks[i].TaskInstance.Variables[j]);
                                        changedVariables.Add(k);
                                    }
                                    else if (Subtasks[subtaskToGround].GetConstants()[k].Name != null &&
                                        Subtasks[subtaskToGround].GetConstants()[k].Name != groundedSubtasks[i].TaskInstance.Variables[j].Name)
                                    {
                                        goto instantiation_failed;
                                    }
                                }
                            }
                        }
                    }

                    if (!InstantiateMainTaskAndSubtasksFromEqualityPreconditions(changedSubtaskVariables, changedVariables, groundedSubtasks, parser))
                    {
                        goto instantiation_failed;
                    }


                    foreach (var rule in subtaskCompletingRules[subtaskToGround])
                    {
                        int nextCost = currentCost + rule.ComputeMinCost();

                        Debug.Assert((Subtasks[subtaskToGround] as AbstractTask).Task.TaskType.Equals(rule.GetCFGRule().MainTask.Task.TaskType));

                        if (cancellationToken.IsCancellationRequested)
                        {
                            yield break;
                        }

                        if (!rule.SetVariablesFromMainTask(Subtasks[subtaskToGround]))
                        {
                            rule.ResetVariables();
                            continue;
                        
                        }

                        if (rule.GetCFGRule().IsEmptyRule)
                        {
                            HashSet<int> nullConstants = new();
                            for (int i = 0; i < Subtasks[subtaskToGround].GetConstants().Length; i++)
                            {
                                if (Constant.ConstantEmpty(Subtasks[subtaskToGround].GetConstants()[i]))
                                {
                                    nullConstants.Add(i);
                                }
                            }


                            foreach (var vars in
                                GroundUngroundedVariables((Subtasks[subtaskToGround] as AbstractTask).GetConstants().
                                Select(x => x.Name).ToList(), (Subtasks[subtaskToGround] as AbstractTask).GetConstants().
                                Select(x => x.Type).ToList()))
                            {
                                if (cancellationToken.IsCancellationRequested)
                                {
                                    yield break;
                                }

                                for (int i = 0; i < vars.Count; i++)
                                {
                                    Subtasks[subtaskToGround].SetVariableValue(i, vars[i]);
                                }

                                rule.GetCFGRule().SetVariablesFromConstants(parser);
                                rule.SetVariablesFromMainTask(Subtasks[subtaskToGround]);

                                if (rule.GetCFGRule().CheckEmptyRuleConstraints(lastSlot))
                                {
                                    double emptyTimelineStartIndex = (subtaskToGround == 0 ? lastEndIndex :
                                        groundedSubtasks[subtaskToGround - 1].EndIndex) + 0.5;
                                    Subplan subplan = new Subplan(new Term((Subtasks[subtaskToGround] as AbstractTask).Task.TaskType.Name,
                                        Subtasks[subtaskToGround].GetConstants()),
                                        emptyTimelineStartIndex, emptyTimelineStartIndex,
                                        (Subtasks[subtaskToGround] as AbstractTask).Task.TaskType);
                                    subplan.Timeline[0] = new Slot(new Term(Subplan.DUMMY_EMPTY_ACTION_NAME, Array.Empty<Constant>()));
                                    subplan.usedActions = Array.Empty<bool>();

                                    groundedSubtasks.Add(subplan);

                                    foreach (var result in
                                        GetGroundedSubtasks(groundedSubtasks, subtaskToGround + 1, parser, startIndex, subtaskCompletingRules,
                                        cancellationToken, maxAllowedCost, nextCost, lastSlot, lastEndIndex))
                                    {
                                        rule.ResetVariables();
                                        if (result != null)
                                        {
                                            yield return result;
                                        }
                                    }

                                    groundedSubtasks.RemoveAt(groundedSubtasks.Count - 1);
                                }

                                foreach (int nullVar in nullConstants)
                                {
                                    Subtasks[subtaskToGround].ResetVariable(nullVar);
                                }
                            }
                        }
                        else
                        {
                            foreach (var subplan in
                                rule.GetGroundedSubplans(parser, nextCost, lastSlot, lastEndIndex, cancellationToken))
                            {
                                if (cancellationToken.IsCancellationRequested)
                                {
                                    yield break;
                                }
                                groundedSubtasks.Add(subplan);

                                 Slot nextSlot = parser.Propagate(lastSlot, subplan.Timeline);

                                foreach (var result in
                                    GetGroundedSubtasks(groundedSubtasks, subtaskToGround + 1, parser, startIndex,
                                    subtaskCompletingRules, cancellationToken, maxAllowedCost, nextCost, nextSlot, subplan.EndIndex))
                                {
                                    rule.ResetVariables();
                                    if (result != null)
                                    {
                                        yield return result;
                                    }
                                    if (!rule.SetVariablesFromMainTask(Subtasks[subtaskToGround]))
                                    {
                                        goto instantiation_failed; 
                                    }
                                }

                                groundedSubtasks.RemoveAt(groundedSubtasks.Count - 1);

                            }
                        }

                        rule.ResetVariables();
                    }

                instantiation_failed:

                    foreach (var i in changedVariables)
                    {
                        Subtasks[subtaskToGround].SetVariable(i, null);
                    }

                    foreach (var item in changedSubtaskVariables)
                    {
                        Subtasks[item.Item1].SetVariable(item.Item2, null);
                    }
                }
            }

            private bool ValidVarTypes(RuleInstance ruleInstance, EarleyParser parser)
            {
                for (int i = 0; i < ruleInstance.Rule.AllVarsTypes.Count; i++)
                {
                    var constantType = ruleInstance.Rule.AllVarsTypes[i];
                    Constant realConstant = InputReader.FindConstant(ruleInstance.AllVars[i], parser.AllConstants);
                    if (!constantType.IsAncestorTo(realConstant.Type))
                    {
                        return false;
                    }
                }

                return true;
            }

            private IEnumerable<Subplan> GetLeafSubplans(EarleyParser parser, int timelinePosition, bool isInPrefix, 
                CancellationToken cancellationToken) // returns all groundings
            {
                if (isInPrefix)
                {
                    var result = parser.GetActionFromPrefix(timelinePosition);
                    Debug.Assert(result.TaskType.Name == (Subtasks[0] as PrimitiveTask).
                        Action.ActionType.ActionTerm.Name);

                    if (parser.IsApplicableToCurrentState(result, out var _, out var _,
                        timelinePosition, out _,
                        out _))
                    {
                        parser.AddToCurrentPlan(new ActionSubplan(result, true,
                            (Subtasks[0] as PrimitiveTask).Action));
                        yield return result;
                        parser.RemoveLastFromCurrentPlan();
                    }
                }
                else
                {
                    Action actionToGround = (Subtasks[0] as PrimitiveTask).Action;
                    Subplan lastSubplan = null;

                    foreach (var tuple in parser.GenerateTasksFromPartiallyInstantiatedAction(actionToGround, timelinePosition))
                    {

                        if (cancellationToken.IsCancellationRequested)
                        {
                            yield break;
                        }

                        if (parser.IsApplicableToCurrentState(tuple.Item1, out var actionsToInsert, 
                            out var correspondingActions,
                            timelinePosition, out _,
                            out _))
                        {
                            parser.AddToCurrentPlan(actionsToInsert.Zip(correspondingActions,
                                (x, y) => new ActionSubplan(x, false, y)).ToArray());


                            yield return tuple.Item1;
                            lastSubplan = tuple.Item1;
                            parser.RemoveLastFromCurrentPlan(actionsToInsert.Count);
                        }
                    }
                }
            }

            internal bool IsLeaf()
            {
                return Subtasks.Length == 1 && Subtasks[0] is PrimitiveTask;
            }
        }

        private void RemoveFromCurrentPlan(int firstIndexInCurrentPlan, int count)
        {
            int originalPlanCount = CurrentPlan.Count;
            List<ActionSubplan> planSuffixToKeep = CurrentPlan.GetRange(firstIndexInCurrentPlan + count, CurrentPlan.Count - count - firstIndexInCurrentPlan);
            RemoveLastFromCurrentPlan(CurrentPlan.Count - firstIndexInCurrentPlan);
            AddActionsBackToPlan(planSuffixToKeep);
            Debug.Assert(CurrentPlan.Count == originalPlanCount - count);
        }

        protected virtual bool RulePreconditionsSatisfied(Subplan subplan, RuleInstance ruleInstance, 
            int timelineIndex,
            List<Subplan> groundedSubtasks, out List<Term> unsatisfiedPosPreconditions,
            out List<Term> unsatisfiedNegPreconditions, out List<Subplan> newActionsToInsert,
            out List<Action> correspondingActions)
        {
            unsatisfiedPosPreconditions = new();
            unsatisfiedNegPreconditions = new();
            newActionsToInsert = new();
            correspondingActions = new();

            bool result = true;
            foreach (var posPrecondTuple in ruleInstance.PosPreConditions)
            {
                if (posPrecondTuple.Item1 > 0) // only rule preconditions are currently supported
                {
                    throw new NotImplementedException(
                        "Only preconditions of the whole rule are supported.");
                }
                var posPrecond = posPrecondTuple.Item2;

                if (!subplan.Timeline[0].PosPreConditions.Contains(posPrecond))
                {
                    unsatisfiedPosPreconditions.Add(posPrecond);
                    result = false;
                }
            }

            foreach (var negPrecondTuple in ruleInstance.NegPreConditions)
            {
                if (negPrecondTuple.Item1 > 0)
                {
                    throw new NotImplementedException(
                        "Only preconditions of the whole rule are supported.");
                }
                var negPrecond = negPrecondTuple.Item2;

                if (subplan.Timeline[0].PosPreConditions.Contains(negPrecond))
                {
                    unsatisfiedNegPreconditions.Add(negPrecond);
                    result = false;
                }
            }

            return result;
        }

        protected virtual Slot Propagate(Slot lastSlot, List<Slot> timeline)
        {
            return CFGRule.Propagate(lastSlot, timeline);
        }

        protected virtual bool CheckWholeTimeline(out List<ActionSubplan> newCurrentPlan)
        {
            newCurrentPlan = CurrentPlan;
            return true;
        }

        protected virtual Subplan GoalTask(List<Subplan> groundedSubtasks)
        {
            return groundedSubtasks[0];
        }
    

#if DEBUG
        void WriteTimeline()
        {
            return;
            using (StreamWriter sw = new StreamWriter("timeline_log.txt", true))
            {
                sw.WriteLine("**********CURRENT PLAN**********");

                sw.Write("INIT: ");
                foreach (var term in InitialState)
                {
                    sw.Write($"{term}; ");
                }
                sw.WriteLine();
                for (int i = 0; i < CurrentPlan.Count; i++)
                {
                    ActionSubplan action = CurrentPlan[i];
                    var slot = CurrentTimeline[i];
                    sw.Write($"{i} : {action.Subplan} : ");
                    foreach (var term in slot.PosPostConditions)
                    {
                        sw.Write($"{term}; ");
                    }
                    sw.WriteLine();
                }
            }
        }
#endif

        internal void ResetCurrentPlan()
        {
            CurrentPlan = new();
            CurrentTimeline = new();
        }

        protected virtual void AddToCurrentPlan(int where, params ActionSubplan[] actions)
        {
            int currentPlanCount = CurrentPlan.Count;
            List<ActionSubplan> currentPlan = CurrentPlan;
            List<ActionSubplan> currentPlanSuffix = CurrentPlan.GetRange(where, CurrentPlan.Count - where);
            CurrentPlan.RemoveRange(where, CurrentPlan.Count - where);
            CurrentTimeline.RemoveRange(where, CurrentTimeline.Count - where);

            AddToCurrentPlan(actions);
            AddActionsBackToPlan(currentPlanSuffix);

            Debug.Assert(CurrentPlan.Count == CurrentTimeline.Count);
            Debug.Assert(CurrentPlan.Count == currentPlanCount + actions.Length);
        }

        void AddActionsBackToPlan(List<ActionSubplan> originalPlanSuffix)
        {
            List<ActionSubplan> suffixActionsToAddToPlan = new();
            int index = -1;
            for (int i = 0; i < originalPlanSuffix.Count; i++)
            {
                if (index == -1 || originalPlanSuffix[i].Subplan.IndexInCurrentPlan == index)
                {
                    index = originalPlanSuffix[i].Subplan.IndexInCurrentPlan;
                    suffixActionsToAddToPlan.Add(originalPlanSuffix[i]);
                }
                else
                {
                    AddToCurrentPlan(suffixActionsToAddToPlan.ToArray());
                    index = originalPlanSuffix[i].Subplan.IndexInCurrentPlan;
                    suffixActionsToAddToPlan = new() { originalPlanSuffix[i] };
                }
            }
            AddToCurrentPlan(suffixActionsToAddToPlan.ToArray());
        }

        protected void AddToCurrentPlan(params ActionSubplan[] actions) 
        {
            int firstActionIndex = CurrentPlan.Count;
            foreach (var action in actions)
            {
                action.Subplan.IndexInCurrentPlan = firstActionIndex;
                CurrentPlan.Add(action);

                Slot newSlot = new();
                CurrentTimeline.Add(newSlot);

                if (CurrentTimeline.Count == 1)
                {
                    newSlot.PosPreConditions = 
                        UnifyConditions(action.Subplan.Timeline[0].PosPreConditions, InitialState);
                }
                else
                {
                    newSlot.PosPreConditions = 
                        UnifyConditions(action.Subplan.Timeline[0].PosPreConditions, 
                        CurrentTimeline[CurrentTimeline.Count - 2].PosPostConditions);
                }
                List<Term> cond = 
                    RemoveConditions(newSlot.PosPreConditions, 
                    action.Subplan.Timeline[0].NegPostConditions);
                newSlot.PosPostConditions = 
                    UnifyConditions(action.Subplan.Timeline[0].PosPostConditions, cond);
            }

        }

        protected virtual void RemoveLastFromCurrentPlan(int count = 1)
        {
            for (int i = 0; i < count; i++)
            {
                CurrentPlan.RemoveAt(CurrentPlan.Count - 1);
                CurrentTimeline.RemoveAt(CurrentTimeline.Count - 1);
            }
        }

        protected List<Term> GetLastSlotConditions()
        {
            return CurrentTimeline.Count == 0 ? InitialState : CurrentTimeline[^1].PosPostConditions;
        }

        protected List<Term> GetLastSlotConditions(int actionInsertionPosition)
        {
            return actionInsertionPosition - 1 < 0 ? InitialState
                : CurrentTimeline[actionInsertionPosition - 1].PosPostConditions;
        }

        protected virtual bool IsApplicableToCurrentState(Subplan action, 
            out List<Subplan> actionsToInsert, out List<Action> correspondingActions, int startIndex,
            out List<Term> unsatisfiedPosPreconditions, out List<Term> unsatisfiedNegPreconditions)
        {
            unsatisfiedPosPreconditions = new();
            unsatisfiedNegPreconditions = new();
            bool applicable = true;

            List<Term> previousSlot = GetLastSlotConditions();
            foreach (var cond in action.Timeline[0].PosPreConditions)
            {
                if (!previousSlot.Contains(cond))
                {

                    applicable = false;
                    unsatisfiedPosPreconditions.Add(cond);
                }
            }

            foreach (var cond in action.Timeline[0].NegPreConditions)
            {
                if (previousSlot.Contains(cond))
                {

                    applicable = false;
                    unsatisfiedNegPreconditions.Add(cond); 
                }

                
            }


            actionsToInsert = new List<Subplan> { action };
            correspondingActions = new List<Action> { new Action(InputReader.FindActionType(AllActionTypes,
                action.TaskType.Name, action.TaskType.NumOfVariables), action.TaskInstance.Variables)};
            return applicable;
        }

        protected virtual List<Subplan> RedistributeSubtasks(List<Subplan> groundedSubtasks)
        {
            return groundedSubtasks;
        }

        private Subplan GetActionFromPrefix(int timelinePosition)
        {
            return PlanPrefix[timelinePosition];
        }

        internal bool IsInPrefix(int timelinePosition)
        {
            return timelinePosition < PlanPrefix.Count;
        }

        private IEnumerable<Tuple<Subplan, Action>> GenerateTasksFromPartiallyInstantiatedAction(Action actionToGround, int timelinePosition)
        {
            return GenerateTasksFromPartiallyInstantiatedAction(actionToGround, AllTaskTypes, AllActionTypes, timelinePosition/* + 1*/,
                AllConstants, AllConstantTypes, CurrentParsingIteration, false);
        }

        internal class Support
        {
            public Support(int domain, Action action)
            {
                Domain = domain;
                Action = action;
            }

            public int Domain { get; }
            public Action Action { get; }

            public override bool Equals(object obj)
            {
                return obj is Support support &&
                       Domain == support.Domain &&
                       Action.Equals(support.Action);
            }

            public override int GetHashCode()
            {
                int hashCode = 1848721880;
                hashCode = hashCode * -1521134295 + Domain;
                hashCode = hashCode * -1521134295 + Action.GetHashCode();
                return hashCode;
            }

            public override string ToString()
            {
                return "a" + Domain + " = " + Action.ToString();
            }

            internal Support Clone()
            {
                return new Support(Domain, Action.Clone());
            }
        }

        internal interface IGroundable
        {
            IEnumerable<Subplan> GetGroundedSubplans(EarleyParser parser, int currentCost, Slot lastSlot, double lastEndIndex, /*Action<int> minCostSetter,*/
                CancellationToken cancellationToken);
            CFGRule GetCFGRule();
            bool IsActionInPrefix(EarleyParser parser);
            int ComputeMinCost();
            int MaxAllowedCost(EarleyParser parser);
            bool SetVariablesFromMainTask(CFGTask cFGTask);
            void ResetVariables();
        }

        internal class QueueItem : IGroundable
        {
            public QueueItem(CFGRule cFGRule, int iterationIndex)
            {
                CFGRule = cFGRule;
                IterationIndex = iterationIndex;

                SubtaskCompletingRules = new HashSet<IGroundable>[CFGRule.Subtasks.Length];
                for (int i = 0; i < CFGRule.Subtasks.Length; i++)
                {
                    SubtaskCompletingRules[i] = new HashSet<IGroundable>();
                }
            }

            public CFGRule CFGRule { get; }
            public int IterationIndex { get; }
            public bool InTable { get; private set; }
            internal HashSet<IGroundable>[] SubtaskCompletingRules { get; }


            internal void AddSubtaskCompletingRule(int subtaskIndex, QueueItem completingRule)
            {
                Debug.Assert(completingRule.CFGRule.MainTask.Task.TaskType.Equals((CFGRule.Subtasks[subtaskIndex] as AbstractTask).Task.TaskType));
                SubtaskCompletingRules[subtaskIndex].Add(completingRule);
            }

            public void AlreadyInTable()
            {
                InTable = true;
            }

            public override bool Equals(object obj)
            {
                return obj != null && obj is QueueItem item &&
                       IterationIndex == item.IterationIndex &&
                       CFGRule.Equals(item.CFGRule);

            }

            public override int GetHashCode()
            {
                int hashCode = 1291648240;
                hashCode = hashCode * -1521134295 + CFGRule.GetHashCode();
                hashCode = hashCode * -1521134295 + IterationIndex;
                return hashCode;
            }

            public override string ToString()
            {
                return CFGRule.ToString() + "; iteration:" + IterationIndex.ToString();
            }



            public IEnumerable<Subplan> GetGroundedSubplans(EarleyParser parser, int currentCost,
                    Slot lastSlot, double lastEndIndex, CancellationToken cancellationToken)
            {
                int maxAllowedCost = MaxAllowedCost(parser);
#if DEBUG
                debugWriter2.WriteLine("Grounding node " + this.ToString());
#endif
                foreach (var subplan in CFGRule.GetGroundedSubplans(parser, this, IterationIndex, SubtaskCompletingRules,
                    maxAllowedCost, currentCost, lastSlot, lastEndIndex, cancellationToken))
                {
#if DEBUG
                    debugWriter2.WriteLine("GROUNDED " + this.ToString() + ": " + subplan.ToString());
#endif
                    yield return subplan;
                }
            }


            internal void CopySubtaskCompletingRulesFrom(QueueItem tableItem)
            {
                for (int i = 0; i < SubtaskCompletingRules.Length; i++)
                {
                    foreach (var rule in tableItem.SubtaskCompletingRules[i])
                    {
                        SubtaskCompletingRules[i].Add(rule);
                    }
                }
            }

            public CFGRule GetCFGRule()
            {
                return CFGRule;
            }

            public bool IsActionInPrefix(EarleyParser parser)
            {
                return parser.IsInPrefix(IterationIndex);
            }

            public int ComputeMinCost()
            {
                return 0;
            }


            public int MaxAllowedCost(EarleyParser parser)
            {
                return int.MaxValue;
            }

            public bool SetVariablesFromMainTask(CFGTask cFGTask)
            {
                return CFGRule.SetVariablesFromMainTask(cFGTask);
            }

            public void ResetVariables()
            {
                CFGRule.ResetVariables();
            }
        }

        class SetItemWithHeuristic : IComparable<SetItemWithHeuristic>
        {
            static long numberOfInstances = 0;
            public SetItemWithHeuristic(QueueItem queueItem, double heuristicValue, int iterationIndex)
            {
                QueueItem = queueItem;
                HeuristicValue = heuristicValue;
                IterationIndex = iterationIndex;
                InstanceID = numberOfInstances++;
            }

            public QueueItem QueueItem { get; }
            public double HeuristicValue { get; }
            public int IterationIndex { get; }
            public long InstanceID { get; }

            public int CompareTo(SetItemWithHeuristic other)
            {
                int result = HeuristicValue.CompareTo(other.HeuristicValue);
                if (result != 0)
                {
                    return result;
                }
                else
                {
                    return InstanceID.CompareTo(other.InstanceID);
                }
            }

            public override bool Equals(object obj) 
            {
                return obj is SetItemWithHeuristic heuristic
                    && QueueItem.Equals(heuristic.QueueItem)
                    && IterationIndex == heuristic.IterationIndex
                    && HeuristicValue == heuristic.HeuristicValue;
            }

            public override int GetHashCode()
            {
                int hashCode = -810741793;
                hashCode = hashCode * -1521134295 + QueueItem.GetHashCode();
                hashCode = hashCode * -1521134295 + HeuristicValue.GetHashCode();
                hashCode = hashCode * -1521134295 + IterationIndex;
                hashCode = hashCode * -1521134295 + InstanceID.GetHashCode();
                return hashCode;
            }
        }

        public List<List<Action>> GetPrunedPlanSuffix(List<Action> planPrefix, int suffixLength, List<ActionType> allActionTypes, List<Rule> allRules,
            List<TaskType> allTaskTypes, CancellationToken cancellationToken)
        {
            List<HashSet<Action>> domains = GetInitialDomains(planPrefix, suffixLength, allActionTypes, out _);
            int desiredPlanLength = planPrefix.Count + suffixLength;
            int iterations = desiredPlanLength;
            List<HashSet<QueueItem>> table = new List<HashSet<QueueItem>>(iterations + 1);
            for (int i = 0; i <= iterations; i++)
            {
                table.Add(new HashSet<QueueItem>());
            }
            Queue<QueueItem> queue = new Queue<QueueItem>();
            HashSet<QueueItem> queueHashSet = new HashSet<QueueItem>();
            InitializeQueue(queue, allTaskTypes, out AbstractTask dummyStartingTask, allRules, out List<Rule> allRulesExtended, queueHashSet);
            for (int i = 0; i <= iterations; i++)
            {

                foreach (QueueItem item in table[i])
                {
                    queue.Enqueue(item);
                    queueHashSet.Add(item);
                }
                while (queue.Count > 0)
                {
                    if (cancellationToken.IsCancellationRequested)
                    {
                        return null;
                    }
                    QueueItem item = queue.Dequeue();

                    queueHashSet.Remove(item);

                    if (!item.InTable && !table[i].Contains(item))
                    {
                        table[i].Add(item); // scanning adds items to table
                    }

                    ProcessItem(item, queue, domains, table, allRulesExtended, i, iterations, queueHashSet);


                }
                if (table[i].Count == 0)
                {
                    return null; // unsatisfiable
                }

            }



            if (AnyStartRuleSuccessfullyParsed(table[iterations], dummyStartingTask, out IEnumerable<Support> allSupports))
            {
                if (suffixLength == 0)
                {
                    return new List<List<Action>>();
                }
                return PrunedDomains(desiredPlanLength, allSupports);
            }
            else
            {
                return null; // unsatisfiable
            }
        }

        internal Subplan RunEarleyParsingAsPlanRecognitionWithHeuristic(List<Action> planPrefix, List<ActionType> allActionTypes, List<Rule> allRules,
            List<TaskType> allTaskTypes, EarleyStateHeuristic heuristic, CancellationToken cancellationToken)
        { // scanner ... add next domain
            List<HashSet<Action>> domains = GetInitialDomains(planPrefix, 1, allActionTypes, out HashSet<Action> allActions); // one additional domain to perform additional scanning
            List<HashSet<QueueItem>> table = new List<HashSet<QueueItem>>(planPrefix.Count + 2);               
            for (int j = 0; j <= planPrefix.Count + 1; j++)
            {
                table.Add(new HashSet<QueueItem>());
            }
            SortedSet<SetItemWithHeuristic> priorityQueue = new SortedSet<SetItemWithHeuristic>();
            Queue<QueueItem> dummyInitQueue = new Queue<QueueItem>();
            InitializeQueue(dummyInitQueue, allTaskTypes, out AbstractTask dummyStartingTask, allRules, out List<Rule> allRulesExtended, 
                new HashSet<QueueItem>());

            foreach (var item in dummyInitQueue)
            {
                priorityQueue.Add(new SetItemWithHeuristic(item, heuristic.ComputeHeuristic(item, 0), 0));
            }

            List<HashSet<SetItemWithHeuristic>> completedByStartIndex = new List<HashSet<SetItemWithHeuristic>>();

            while (priorityQueue.Count > 0)
            {
                if (cancellationToken.IsCancellationRequested)
                {
                    return null;
                }
                SetItemWithHeuristic item = priorityQueue.Min;
                priorityQueue.Remove(item);
                int i = item.IterationIndex;
                if (!item.QueueItem.InTable && !table[i].Contains(item.QueueItem))
                {
                    table[i].Add(item.QueueItem);
                }
                Subplan goal = ProcessItem(item, priorityQueue, domains, table, allRulesExtended, heuristic, allActions, 
                    completedByStartIndex, planPrefix.Count, dummyStartingTask,
                    cancellationToken, this);

                if (goal != null)
                {
                    return goal;
                }
            }

            return null;
        }

        private Subplan ProcessItem(SetItemWithHeuristic setItem, SortedSet<SetItemWithHeuristic> priorityQueue, List<HashSet<Action>> domains, List<HashSet<QueueItem>> table,
            List<Rule> allRules, EarleyStateHeuristic heuristic, HashSet<Action> allActions, 
            List<HashSet<SetItemWithHeuristic>> completedByStartIndex, int prefixLength, AbstractTask dummyStartingTask, 
            CancellationToken cancellationToken, EarleyParser parser)
        {
            QueueItem item = setItem.QueueItem;
            int iterationIndex = setItem.IterationIndex;

            if (!item.CFGRule.TryGetNextTask(out CFGTask nextTask)) // rule finished
            {
                if (IsPossibleGoal(item, dummyStartingTask, true, prefixLength, iterationIndex))
                {
                    Subplan goal = TryExtractGoal(item, this, DummyInitSlot, cancellationToken);
                    if (goal != null)
                    {
                        return goal;
                    }
                }

                Completion(item, null, table, null, iterationIndex, priorityQueue, true, heuristic, completedByStartIndex, setItem);
            }
            else
            {
                if (nextTask is PrimitiveTask && domains.Count <= iterationIndex)
                {
                    domains.Add(allActions);
                }

                if (nextTask is PrimitiveTask primitiveTask
                && TryGetApplicableAction(domains[iterationIndex], primitiveTask, out Action action))
                {
                    Scanning(item, action, table, iterationIndex, true, priorityQueue, heuristic);
                }
                else if (nextTask is AbstractTask)
                {
                    Prediction(item, allRules, null, table, iterationIndex, parser, null, true, heuristic, priorityQueue, completedByStartIndex);
                }
            }
            return null;
        }

        protected Subplan RunEarleyParsingAsPlanVerification(List<Action> planPrefix, List<ActionType> allActionTypes, List<Rule> allRules,
            List<TaskType> allTaskTypes, CancellationToken cancellationToken, Task rootTask = null)
        {
            List<HashSet<Action>> domains = GetInitialDomains(planPrefix, 1, allActionTypes, out HashSet<Action> allActions); // one additional domain to perform additional scanning
            List<HashSet<QueueItem>> table = new List<HashSet<QueueItem>>(planPrefix.Count + 2);               
            for (int j = 0; j <= planPrefix.Count + 1; j++)
            {
                table.Add(new HashSet<QueueItem>());
            }
            Queue<QueueItem> queue = new Queue<QueueItem>();
            HashSet<QueueItem> queueHashSet = new HashSet<QueueItem>();
            InitializeQueue(queue, allTaskTypes, out AbstractTask dummyStartingTask, allRules, out List<Rule> allRulesExtended, queueHashSet,
                rootTask);

            int i; // iteration index
            Subplan goalTask = null;
            // Initial iterations only with plan prefix:
            for (i = 0; i <= planPrefix.Count; i++)
            {
#if DEBUG
                Console.WriteLine($"iteration {i}");
#endif
                CurrentParsingIteration = i;
                if (cancellationToken.IsCancellationRequested)
                {
                    return null;
                }
                OneIteration(i, cancellationToken, domains, table, allRulesExtended, queue, queueHashSet, out goalTask, 
                    i == PlanPrefix.Count, dummyStartingTask);

                if (table[i].Count == 0)
                {
                    Debugger.Break();
                }
            }


            if (goalTask == null)
            {
                foreach (var item in table[table.Count - 2])
                {
                    if (IsPossibleGoal(item, dummyStartingTask))
                    {
                        Subplan subplan = TryExtractGoal(item, this, DummyInitSlot, cancellationToken);
                        if (subplan != null)
                        {
                            goalTask = subplan;
                            break;
                        }
                    }
                }
            }

#if DEBUG
            if (goalTask == null)
            {
                Console.WriteLine("\tTABLE:");
                foreach (var t in table[table.Count - 2])
                {
                    Console.WriteLine("\t\t" + t);
                }
            }
#endif

            return goalTask;

        }

        private Subplan RunEarleyParsingAsPlanRecognition(List<Action> planPrefix, List<ActionType> allActionTypes, List<Rule> allRules,
            List<TaskType> allTaskTypes, CancellationToken cancellationToken)
        {
            List<HashSet<Action>> domains = GetInitialDomains(planPrefix, 1, allActionTypes, out HashSet<Action> allActions); // one additional domain to perform additional scanning
            List<HashSet<QueueItem>> table = new List<HashSet<QueueItem>>(planPrefix.Count + 2);      
            for (int j = 0; j <= planPrefix.Count + 1; j++)
            {
                table.Add(new HashSet<QueueItem>());
            }
            Queue<QueueItem> queue = new Queue<QueueItem>();
            HashSet<QueueItem> queueHashSet = new HashSet<QueueItem>();
            InitializeQueue(queue, allTaskTypes, out AbstractTask dummyStartingTask, allRules, out List<Rule> allRulesExtended, queueHashSet);

            int desiredPlanLength = planPrefix.Count;
            int i; // iteration index
            // Initial iterations only with plan prefix:
            for (i = 0; i <= planPrefix.Count; i++)
            {
                CurrentParsingIteration = i;
                if (cancellationToken.IsCancellationRequested)
                {
                    return null;
                }
                OneIteration(i, cancellationToken, domains, table, allRulesExtended, queue, queueHashSet, out _);

                if (table[i].Count == 0)
                {
                    Debugger.Break();
                }
            }

            while (true) // until no goal is found
            {
#if DEBUG
                debugWriter.WriteLine(i + ": table[" + (i - 1) + "]: " + table[i - 1].Count);
                debugWriter.WriteLine(i + ": table[" + i + "]: " + table[i].Count);
#endif

                if (cancellationToken.IsCancellationRequested)
                {
                    return null;
                }

                Subplan goalTask = FindGoalTask(table[desiredPlanLength], dummyStartingTask, cancellationToken);
                if (goalTask != null)
                {
                    return goalTask;
                }

                // Plan extension:
                desiredPlanLength++;
                table.Add(new HashSet<QueueItem>());
                domains.Add(allActions);

                Console.WriteLine("Level: " + i);

                OneIteration(i, cancellationToken, domains, table, allRulesExtended, queue, queueHashSet, out _);
                i++;
                CurrentParsingIteration = i;
            }
        }

        protected Subplan TryExtractGoal(IGroundable queueItem, EarleyParser parser, Slot dummyInitStateSlot,
            CancellationToken cancellationToken)
        {
            return queueItem.GetGroundedSubplans(parser, 0, dummyInitStateSlot, -1, cancellationToken).FirstOrDefault(); 
        }

        protected static bool IsPossibleGoal(QueueItem queueItem, AbstractTask dummyStartingTask, bool heuristicSelection = false, int prefixLength = -1, int endIterationIndex = -1)
        {
            if (heuristicSelection)
            {
                if (endIterationIndex < prefixLength)
                {
                    return false;
                }
            }
            return queueItem.IterationIndex == 0 && queueItem.CFGRule.Finished() && queueItem.CFGRule.MainTask.Task.Equals(dummyStartingTask.Task);
        }

        private Subplan FindGoalTask(HashSet<QueueItem> queueItems, AbstractTask dummyStartingTask, CancellationToken cancellationToken)
        {
            foreach (QueueItem queueItem in queueItems)
            {
                if (cancellationToken.IsCancellationRequested)
                {
                    return null;
                }

                if (IsPossibleGoal(queueItem, dummyStartingTask))
                {
                   

                    Subplan subplan = TryExtractGoal(queueItem, this, DummyInitSlot, cancellationToken);
                    if (subplan != null)
                    {
                        return subplan;
                    }
                }
            }
            return null;
        }

        protected bool OneIteration(int i, CancellationToken cancellationToken, List<HashSet<Action>> domains,
            List<HashSet<QueueItem>> table,
            List<Rule> allRulesExtended, Queue<QueueItem> queue, HashSet<QueueItem> queueHashSet, out Subplan result,
            bool finalIteration = false, AbstractTask dummyStartingTask = null)
        {
            result = null;
            foreach (QueueItem item in table[i])
            {
                queue.Enqueue(item);
                queueHashSet.Add(item);
            }
            while (queue.Count > 0)
            {
                if (cancellationToken.IsCancellationRequested)
                {
                    return false;
                }
                QueueItem item = queue.Dequeue();

                queueHashSet.Remove(item);

                if (!item.InTable && !table[i].Contains(item)) // scanning adds items to table
                {
                    AddToTable(i, item, table);
                }

                if (finalIteration)
                {
                    if (IsPossibleGoal(item, dummyStartingTask))
                    {
                        Subplan subplan = TryExtractGoal(item, this, DummyInitSlot, cancellationToken);
                        if (subplan != null)
                        {
                            result = subplan;
                            return true;
                        }
                    }
                }
#if DEBUG
                Console.WriteLine($"Processing {item}");
#endif
                ProcessItem(item, queue, domains, table, allRulesExtended, i, int.MaxValue, queueHashSet, true);
            }
#if DEBUG
            debugWriter.WriteLine("iteration {0}:", i);
            debugWriter.WriteLine("\ttable[{0}]:", i);
            foreach (QueueItem item in table[i])
            {
                debugWriter.WriteLine("\t" + item);
            }
            debugWriter.WriteLine("\ttable[{0}]:", i + 1);
            foreach (QueueItem item in table[i + 1])
            {
                debugWriter.WriteLine("\t" + item);
            }
            debugWriter.WriteLine("______________________________________________________________________________________________________");
#endif

            if (table[i].Count == 0)
            {
                Debugger.Break();
                return false; // unsatisfiable
            }

            return true; // successfully finished iteration
        }

        protected virtual bool ApplyConditionsAndCheckValidity(Subplan subplan,
                RuleInstance ruleInstance,
                List<Subplan> subtasks, EarleyParser parser,
                int indexToCheckPreconditionsFrom = 0 /*important for TIHTN**/)
        {
            return CFGRule.ApplyConditionsAndCheckValidity(subplan, ruleInstance, subtasks,
                parser, indexToCheckPreconditionsFrom);
        }

        virtual protected void AddToTable(int i, QueueItem item, List<HashSet<QueueItem>> table)
        {
            table[i].Add(item);
        }

        private List<List<Action>> PrunedDomains(int desiredPlanLength, IEnumerable<Support> allSupports)
        {
            List<List<Action>> result = new List<List<Action>>(desiredPlanLength); 
            List<Dictionary<ActionType, List<Action>>> actionsByActionType = new List<Dictionary<ActionType, List<Action>>>();
            for (int i = 0; i < desiredPlanLength; i++)
            {
                result.Add(new List<Action>());
                actionsByActionType.Add(new Dictionary<ActionType, List<Action>>());
            }
            foreach (Support support in allSupports) 
            {
                if (!actionsByActionType[support.Domain].TryGetValue(support.Action.ActionType, out List<Action> list))
                {
                    list = new List<Action>();
                    actionsByActionType[support.Domain].Add(support.Action.ActionType, list);
                }
                bool addNewAction = true;
                List<Action> actionsToRemove = new List<Action>();
                foreach (Action action in list)
                {
                    if (action.Subsumes(support.Action))
                    {
                        addNewAction = false;
                        break;
                    }
                    else if (support.Action.Subsumes(action))
                    {
                        actionsToRemove.Add(action);
                    }
                }
                foreach (Action action in actionsToRemove)
                {
                    list.Remove(action);
                }
                if (addNewAction)
                {
                    list.Add(support.Action);
                }
            }

            for (int i = 0; i < desiredPlanLength; i++)
            {
                foreach (var list in actionsByActionType[i].Values)
                {
                    result[i].AddRange(list);
                }
            }

            return result;
        }

        private bool AnyStartRuleSuccessfullyParsed(HashSet<QueueItem> queueItems, AbstractTask dummyStartingTask, out IEnumerable<Support> allSupports)
        {
            HashSet<Support> foundSupports = new HashSet<Support>();

            foreach (QueueItem queueItem in queueItems)
            {
                if (queueItem.IterationIndex == 0 && queueItem.CFGRule.Finished() && queueItem.CFGRule.MainTask.Task.Equals(dummyStartingTask.Task))
                {
                    foundSupports.UnionWith(queueItem.CFGRule.GetSupports());
                }
            }

            allSupports = foundSupports;
            return foundSupports.Count > 0;
        }

        void ProcessItem(QueueItem item, Queue<QueueItem> queue, List<HashSet<Action>> domains, List<HashSet<QueueItem>> table, List<Rule> allRules,
            int iterationIndex, int totalIterations, HashSet<QueueItem> queueHashSet, bool exceedingIterationLimitAllowed = false)
        {
            if (!item.CFGRule.TryGetNextTask(out CFGTask nextTask)) // rule finished
            {
                Completion(item, queue, table, queueHashSet, iterationIndex);
            }
            else if ((exceedingIterationLimitAllowed || iterationIndex < totalIterations) && nextTask is PrimitiveTask primitiveTask
                && TryGetApplicableAction(domains[iterationIndex], primitiveTask, out Action action))
            {
                Scanning(item, action, table, iterationIndex);
            }
            else if (nextTask is AbstractTask) 
            {
                Prediction(item, allRules, queue, table, iterationIndex, this, queueHashSet);
            }
        }

        private void Prediction(QueueItem item, List<Rule> allRules, Queue<QueueItem> queue, List<HashSet<QueueItem>> table, 
            int iterationIndex, EarleyParser parser, 
            HashSet<QueueItem> queueHashSet, bool heuristicSelection = false, EarleyStateHeuristic heuristic = null, 
            SortedSet<SetItemWithHeuristic> priorityQueue = null,
            List<HashSet<SetItemWithHeuristic>> completedByStartIndex = null)
        {

            item.CFGRule.TryGetNextTask(out CFGTask nextTask);
            TaskType desiredTaskType = (nextTask as AbstractTask).Task.TaskType;

            bool foundCompletedRules = false;
            if (heuristicSelection && completedByStartIndex.Count > iterationIndex)
            {
                foreach(var completedRule in completedByStartIndex[iterationIndex])
                {
                    if (CFGTask.SameTypeTasks(completedRule.QueueItem.CFGRule.MainTask, nextTask) && 
                        NonConflictingInstantiations(completedRule.QueueItem.CFGRule.MainTask.GetConstants(),
                        nextTask.GetConstants()))
                    {
                        foundCompletedRules = true;
                        priorityQueue.Add(completedRule); 
                    }
                }
            }

            if (!heuristicSelection || !foundCompletedRules)
            {
                foreach (var rule in EnumerateRulesByMainTask(allRules, desiredTaskType))
                {
                        CFGTask[] subtasks = GetSubtasksForRule(nextTask as AbstractTask, rule, item.CFGRule);
                        CFGRule cFGRule = new CFGRule(nextTask.Clone() as AbstractTask, subtasks, rule, parser);
                        QueueItem queueItem = new QueueItem(cFGRule, iterationIndex);
                        if (!heuristicSelection)
                        {
                            if (!table[iterationIndex].Contains(queueItem) && !queueHashSet.Contains(queueItem))
                            {
                                queue.Enqueue(queueItem);
                                queueHashSet.Add(queueItem);
                            }
                        }
                        else
                        {
                            var newSetItem = new SetItemWithHeuristic(queueItem, heuristic.ComputeHeuristic(queueItem, iterationIndex), 
                                iterationIndex);

                            priorityQueue.Add(newSetItem);
                        }
                }
            }
        }

        protected virtual IEnumerable<Rule> EnumerateRulesByMainTask(List<Rule> allRules, TaskType desiredTaskType)
        {
            foreach (Rule rule in allRules)
            {
                if (rule.MainTaskType.Equals(desiredTaskType))
                {
                    yield return rule;
                }
            }
        }

        protected static CFGTask[] GetSubtasksForRule(AbstractTask mainTask, Rule rule, CFGRule parentRule)
        {
            CFGTask[] result = new CFGTask[rule.ArrayOfReferenceLists.Length];
            for (int i = 0; i < result.Length; i++)
            {
                if (rule.TaskTypeArray[i] is ActionTaskType actionTaskType)
                {
                    Action action = new Action(actionTaskType.ActionType);
                    result[i] = new PrimitiveTask(action);
                }
                else
                {
                    Task task = new Task(rule.TaskTypeArray[i]);
                    result[i] = new AbstractTask(task);
                }

            }

            for (int i = 0; i < rule.MainTaskReferences.Count; i++) // main task variables
            {
                if (mainTask.Task.TaskInstance[i] != null)
                {
                    int variableIndex = rule.MainTaskReferences[i];
                    Constant constant = mainTask.Task.TaskInstance[i];
                    for (int j = 0; j < rule.ArrayOfReferenceLists.Length; j++) // subtasks
                    {
                        for (int k = 0; k < rule.ArrayOfReferenceLists[j].Count; k++) // subtask variables
                        {
                            if (rule.ArrayOfReferenceLists[j][k] == variableIndex)
                            {
                                result[j].SetVariable(k, constant);
                            }
                            if (rule.AllVarsTypes.Count > 0 && result[j].GetConstants()[k].Type.
                                IsAncestorTo(rule.AllVarsTypes[rule.ArrayOfReferenceLists[j][k]]))
                            {
                                result[j].SetVariable(k, new Constant(result[j].GetConstants()[k].Name, 
                                    rule.AllVarsTypes[rule.ArrayOfReferenceLists[j][k]]));
                            }
                        }
                    }

                }
            }
        
        
            return result;
        }

        protected virtual void AddNewTableColumn(List<HashSet<QueueItem>> table)
        {
            table.Add(new HashSet<QueueItem>());
        }

        private void Scanning(QueueItem item, Action action, List<HashSet<QueueItem>> table, int iterationIndex, bool heuristicSelection = false,
            SortedSet<SetItemWithHeuristic> priorityQueue = null, EarleyStateHeuristic heuristic = null)
        {
#if DEBUG
            //Console.WriteLine(item + " (scanning)");
#endif
            CFGRule cFGRule = CloneAndFillVarsBySubtaskInstantiation(item.CFGRule, action.ActionInstance, 
                item.CFGRule.CurrentSubtaskIndex, this);
            cFGRule.TryGetNextTask(out var nextTask);
            Support support = new Support(iterationIndex, action);
            (nextTask as PrimitiveTask).AddSupportFromAction(support);
            cFGRule.IncrementCurrentSubtaskIndex();
            QueueItem newQueueItem = new QueueItem(cFGRule, item.IterationIndex); 
            newQueueItem.CopySubtaskCompletingRulesFrom(item);

            if (table.Count == iterationIndex + 1)
            {
                AddNewTableColumn(table);
            }

            AddToTable(iterationIndex + 1, newQueueItem, table);

            newQueueItem.AlreadyInTable();

            if (heuristicSelection)
            {
                priorityQueue.Add(new SetItemWithHeuristic(newQueueItem, heuristic.ComputeHeuristic(newQueueItem, iterationIndex + 1), 
                    iterationIndex + 1));
            }
        }

        protected static bool TryGetApplicableAction(HashSet<Action> actions, PrimitiveTask primitiveTask, out Action applicableAction)
        {
            Action action = primitiveTask.Action;
            Action emptyAction = new(action.ActionType);
            if (!actions.TryGetValue(action, out Action foundAction) && !actions.TryGetValue(emptyAction, out foundAction))
            {
                foreach (Action a in actions)
                {
                    if (Action.SameTypeActions(action, a) && NonConflictingInstantiations(action.ActionInstance, a.ActionInstance))
                    {
                        foundAction = a;
                    }
                }
            }

            if (foundAction != null)
            {
                applicableAction = MergeInstantiations(foundAction, action);
                return true;
            }
            else
            {
                applicableAction = null;
                return false;
            }
        }

        private static Action MergeInstantiations(Action a1, Action a2)
        {
            if (Action.SameTypeActions(a1, a2))
            {
                Action result = new Action(a1.ActionType);
                for (int i = 0; i < a1.ActionInstance.Length; i++)
                {
                    if (!Constant.ConstantEmpty(a1.ActionInstance[i]))
                    {
                        if (!Constant.ConstantEmpty(a2.ActionInstance[i]))
                        {
                            if (a1.ActionInstance[i].Name == a2.ActionInstance[i].Name)
                            {
                                result.SetVariable(i, a1.ActionInstance[i]);
                            }
                            else
                            {
                                return null;
                            }
                        }
                        else
                        {
                            result.SetVariable(i, a1.ActionInstance[i]);
                        }
                    }
                    else
                    {
                        result.SetVariable(i, a2.ActionInstance[i]);
                    }
                }
                return result;
            }
            else
            {
                Debug.Assert(false);
                return null;
            }
        }

        protected static bool NonConflictingInstantiations(Constant[] parentTypeConstants, Constant[] childTypeConstants)
        {
            for (int i = 0; i < parentTypeConstants.Length; i++)
            {
                if (!(parentTypeConstants[i].Name == null || parentTypeConstants[i].Name.Length == 0 ||
                    childTypeConstants[i].Name == null || childTypeConstants[i].Name.Length == 0 ||
                    parentTypeConstants[i].Name == childTypeConstants[i].Name) ||
                    (parentTypeConstants[i].Name != childTypeConstants[i].Name &&
                    !parentTypeConstants[i].Type.Equals(childTypeConstants[i].Type)
                    && !parentTypeConstants[i].Type.IsAncestorTo(childTypeConstants[i].Type)))
                {
                    return false;
                }
            }
            return true;
        }

        protected virtual IEnumerable<QueueItem> EnumerateTableItems(int iterationIndex, List<HashSet<QueueItem>> table,
            CFGTask mainTask)
        {
            foreach (QueueItem tableItem in table[iterationIndex])
            {
                yield return tableItem;
            }
        }

        private void Completion(QueueItem queueItem, Queue<QueueItem> queue, List<HashSet<QueueItem>> table, HashSet<QueueItem> queueHashSet, int iterationIndex,
            SortedSet<SetItemWithHeuristic> priorityQueue = null, bool heuristicSelection = false, EarleyStateHeuristic heuristic = null, 
            List<HashSet<SetItemWithHeuristic>> completedByStartIndex = null, SetItemWithHeuristic setItem = null)
        {
#if DEBUG
            Console.WriteLine(queueItem + " (completion)");
#endif
            if (COMPUTING_SUPPORTS)
            {
                queueItem.CFGRule.MoveSupportsToMainTask();
            }

            if (heuristicSelection)
            {
                while (completedByStartIndex.Count <= queueItem.IterationIndex)
                {
                    completedByStartIndex.Add(new HashSet<SetItemWithHeuristic>());
                }
                completedByStartIndex[queueItem.IterationIndex].Add(setItem);
            }

            foreach (QueueItem tableItem in EnumerateTableItems(queueItem.IterationIndex, table, queueItem.CFGRule.MainTask))
            {
                if (tableItem.CFGRule.TryGetNextTask(out CFGTask nextTask) && CFGTask.SameTypeTasks(nextTask, queueItem.CFGRule.MainTask) &&
                    NonConflictingInstantiations(nextTask.GetConstants(), queueItem.CFGRule.MainTask.GetConstants())) 
                {
                    CFGRule newCFGRule = CloneAndFillVarsBySubtaskInstantiation(tableItem.CFGRule, 
                        queueItem.CFGRule.MainTask.Task.TaskInstance,
                        tableItem.CFGRule.CurrentSubtaskIndex, this);
                    newCFGRule.TryGetNextTask(out nextTask);
                    nextTask.CloneSupportsFromOtherTask(queueItem.CFGRule.MainTask);
                    newCFGRule.IncrementCurrentSubtaskIndex();
                    QueueItem newQI = new QueueItem(newCFGRule, tableItem.IterationIndex);

                    if (!table[iterationIndex].TryGetValue(newQI, out QueueItem existingItem) && 
                        (heuristicSelection || !queueHashSet.Contains(newQI)))
                    {
                        newQI.CopySubtaskCompletingRulesFrom(tableItem);
                        newQI.AddSubtaskCompletingRule(tableItem.CFGRule.CurrentSubtaskIndex, queueItem);

                        if (!heuristicSelection)
                        {
                            queue.Enqueue(newQI);
                            queueHashSet.Add(newQI);
                        }
                        else
                        {
                            bool b = priorityQueue.Add(new SetItemWithHeuristic(newQI, heuristic.ComputeHeuristic(newQI, iterationIndex), iterationIndex));
                        }
                    }
                    if (existingItem != null)
                    {
                        existingItem.AddSubtaskCompletingRule(tableItem.CFGRule.CurrentSubtaskIndex, queueItem);

#if DEBUG
                        for (int i = 0; i < existingItem.SubtaskCompletingRules.Length; i++)
                        {
                            HashSet<IGroundable> completingRules = existingItem.SubtaskCompletingRules[i];
                            foreach (var rule in completingRules)
                            {
                                Debug.Assert(existingItem.CFGRule.Subtasks[i].ToString() == rule.GetCFGRule().MainTask.ToString());
                            }

                            if (i < tableItem.CFGRule.CurrentSubtaskIndex)
                            {
                                Debug.Assert(tableItem.SubtaskCompletingRules[i].SetEquals(completingRules));
                            }
                            else if (i == tableItem.CFGRule.CurrentSubtaskIndex)
                            {
                                Debug.Assert(tableItem.SubtaskCompletingRules[i].IsProperSubsetOf(completingRules));
                            }
                        }
#endif
                    }
                }
            }
        }

        private static void FillVarsBySubtaskOrMainTaskInstantiation(CFGRule cFGRule, Constant[] constants, int subtaskIndex /* -1 for main task */)
        {
            List<int> instantiatedTaskReferenceList;
            if (subtaskIndex == -1)
            {
                instantiatedTaskReferenceList = cFGRule.Rule.MainTaskReferences;
            }
            else
            {
                if (cFGRule.Rule.ArrayOfReferenceLists.Length <= subtaskIndex)
                {
                    instantiatedTaskReferenceList = new();
                }
                else
                {
                    instantiatedTaskReferenceList = cFGRule.Rule.ArrayOfReferenceLists[subtaskIndex];
                }
            }
            HashSet<int> changedSubtasks = new HashSet<int>();
            for (int i = 0; i < instantiatedTaskReferenceList.Count; i++)
            {
                if (Constant.ConstantEmpty(constants[i]))
                {
                    continue;
                }

                int reference = instantiatedTaskReferenceList[i];

                for (int j = 0; j < cFGRule.Rule.MainTaskReferences.Count; j++)
                {
                    if (cFGRule.Rule.MainTaskReferences[j] == reference)
                    {
                        cFGRule.MainTask.SetVariable(j, constants[i]);
                    }
                }

                for (int j = 0; j < cFGRule.Subtasks.Length; j++)
                {
                    CFGTask otherSubtask = cFGRule.Subtasks[j];
                    List<int> referenceList = cFGRule.Rule.ArrayOfReferenceLists[j];
                    for (int k = 0; k < referenceList.Count; k++)
                    {
                        if (referenceList[k] == reference)
                        {
                            otherSubtask.SetVariable(k, constants[i]);
                            changedSubtasks.Add(j);
                        }
                    }
                }
            }

            if (COMPUTING_SUPPORTS)
            {
                // Setting supports:
                foreach (int i in changedSubtasks)
                {
                    cFGRule.Subtasks[i].SetSupportVariables();
                }

                cFGRule.MoveSupportsToMainTask();
            }
        }

        protected static CFGRule CloneAndFillVarsBySubtaskInstantiation(CFGRule cFGRule, Constant[] instantiation,
            int subtaskInstantiationIndex, EarleyParser parser)
        {
            return CloneAndFillVarsByTaskInstantiation(cFGRule, instantiation, subtaskInstantiationIndex, parser);
        }

        private CFGRule CloneAndFillVarsByMainTaskInstantiation(CFGRule cFGRule, Constant[] instantiation, EarleyParser parser)
        {
            return CloneAndFillVarsByTaskInstantiation(cFGRule, instantiation, -1, parser);
        }

        protected static CFGRule CloneAndFillVarsByTaskInstantiation(CFGRule cFGRule, Constant[] instantiation, 
            int mainTaskOrSubtaskInstantiationIndex, EarleyParser parser)
        {
            CFGRule cFGRuleClone = cFGRule.Clone(parser);
            FillVarsBySubtaskOrMainTaskInstantiation(cFGRuleClone, instantiation, mainTaskOrSubtaskInstantiationIndex);
            return cFGRuleClone;
        }

        protected virtual void AddToRules(List<Rule> allRulesExtended, Rule rule)
        {
            allRulesExtended.Add(rule);
        }

        protected void InitializeQueue(Queue<QueueItem> queue, List<TaskType> allTaskTypes, out AbstractTask dummyStartingTask, 
            List<Rule> allRules,
            out List<Rule> allRulesExtended, HashSet<QueueItem> queueHashSet, Task rootTask = null)
        {
            allRulesExtended = new List<Rule>(allRules);
            TaskType dummyStartingTaskType = new TaskType("start_dummy", 0);
            dummyStartingTask = new AbstractTask(new Task(dummyStartingTaskType));

            TaskType secondDummyTaskType = new TaskType("second_dummy", 0);
            AbstractTask dummySecondTask = new AbstractTask(new Task(secondDummyTaskType));

            AllDummyTaskTypes = new List<TaskType> { dummyStartingTaskType, secondDummyTaskType };

            if (rootTask != null)
            {
                CFGRule startingRule = new CFGRule(dummyStartingTask, new CFGTask[] { new AbstractTask(rootTask) }, new Rule
                {
                    MainTaskType = dummyStartingTaskType,
                    TaskTypeArray = new TaskType[] { rootTask.TaskType },
                    ArrayOfReferenceLists = new List<int>[1] { new List<int>(0) },
                    MainTaskReferences = new List<int>(0)
                }, this);
                QueueItem queueItem = new QueueItem(startingRule, 0);
                queue.Enqueue(queueItem);
                queueHashSet.Add(queueItem);
            }

            else
            {
                foreach (var taskType in allTaskTypes)
                {
                    Rule dummyRule = new Rule
                    {
                        MainTaskType = secondDummyTaskType,
                        TaskTypeArray = new TaskType[] { taskType },
                        ArrayOfReferenceLists = new List<int>[1] { Enumerable.Range(0, taskType.NumOfVariables).ToList() },
                        MainTaskReferences = new List<int>(0)
                    };
                    AddToRules(allRulesExtended, dummyRule);
                }

                CFGRule dummyStartingRule = new CFGRule(dummyStartingTask, new CFGTask[] { dummySecondTask }, new Rule
                {
                    MainTaskType = dummyStartingTaskType,
                    TaskTypeArray = new TaskType[] { secondDummyTaskType },
                    ArrayOfReferenceLists = new List<int>[1] { new List<int>(0) },
                    MainTaskReferences = new List<int>(0)
                }, this);
                QueueItem queueItem = new QueueItem(dummyStartingRule, 0);
                queue.Enqueue(queueItem);
                queueHashSet.Add(queueItem);
            }
        }

        protected List<HashSet<Action>> GetInitialDomains(List<Action> planPrefix, int suffixLength, List<ActionType> allActionTypes, out HashSet<Action> allActions)
        {
            List<HashSet<Action>> result = new List<HashSet<Action>>(planPrefix.Count + suffixLength);
            for (int i = 0; i < planPrefix.Count; i++)
            {
                result.Add(new HashSet<Action>() { planPrefix[i] });
            }

            allActions = new HashSet<Action>(allActionTypes.Count);
            foreach (ActionType actionType in allActionTypes)
            {
                allActions.Add(new Action(actionType));
            }

            for (int i = planPrefix.Count; i < planPrefix.Count + suffixLength; i++)
            {
                result.Add(allActions);
            }

            return result;
        }

        internal bool Init(List<Term> plan, List<TaskType> allTaskTypes, List<ActionType> allActionTypes, List<Constant> allConstants, 
            List<Term> initState)
        {
            PlanPrefix = new List<Subplan>();
            int i = 0;
            int size = plan.Count;
            Slot prevSlot = null;
            List<Subplan> newTasks = new List<Subplan>();
            foreach (Term a in plan)
            {
                Subplan t = CreateTaskFromAction(a, allTaskTypes, allActionTypes, i, size, prevSlot, allConstants);
                if (t == null)
                {
                    return false;
                }
                i++;
                PlanPrefix.Add(t);
                newTasks.Add(t);
                t.Iteration = -1; //As these are basic actions we must give them low iteration. So that when we create tasks on iteration 0 it will work.
                if (i == 1)
                {
                    PlanPrefix[0].GetSlot(0).PosPreConditions = UnifyConditions(PlanPrefix[0].GetSlot(0).PosPreConditions, initState); // We assume init state has only positive conditions. If it has negative we can simply ignore them as negative just means not in the list of positive.
                    List<Term> c1 = RemoveConditions(PlanPrefix[0].GetSlot(0).PosPreConditions, PlanPrefix[0].GetSlot(0).NegPostConditions);
                    PlanPrefix[0].GetSlot(0).PosPostConditions = UnifyConditions(PlanPrefix[0].GetSlot(0).PosPostConditions, c1);
                    prevSlot = PlanPrefix[0].GetSlot(0);
                }
                else
                {
                    prevSlot = t.GetSlot(0);
                }

            }

            string name = "FakeSubplanForEmptySubtasks";
            Constant[] constants = new Constant[1];
            Subplan prefixTimeline = MergePlans(newTasks, new Term(name, constants), null, null);  
            Propagate(ref prefixTimeline.Timeline);

            PrefixTimeline = prefixTimeline.Timeline;
            return true;
        }


        internal virtual bool VerifyPlanByEarleyParser(List<Term> plan, List<Action> planPrefix, List<Term> initialState, List<Rule> rules,
            out Rule finalRule, out Subplan finalSubtask, out List<int> addedActionsByIteration, CancellationToken cancellationToken,
            Task rootTask = null,
            EarleyStateHeuristic heuristic = null)
        {
            List<Rule> rulesExpandedByExplicitOrdering = ExpandExplicitSubtaskOrdering(rules);
            CreateConstantTypeInstances(AllConstants, AllConstantTypes);

            if (!Init(plan, AllTaskTypes, AllActionTypes, AllConstants, initialState))
            {
                finalRule = null;
                finalSubtask = null;
                addedActionsByIteration = null;
                return false;
            }

            Subplan subplan = RunEarleyParsingAsPlanVerification(planPrefix, AllActionTypes, rulesExpandedByExplicitOrdering, AllTaskTypes,
                    cancellationToken, rootTask);

            if (cancellationToken.IsCancellationRequested)
            {
                finalRule = null;
                finalSubtask = null;
                addedActionsByIteration = null;
                return false;
            }

            addedActionsByIteration = new List<int>(); // irrelevant here
            finalSubtask = subplan;

            if (subplan != null)
            {
                finalRule = subplan.LastRuleInstance.Rule;
                return true;
            }
            else
            {
                finalRule = null;
                return false;
            }
        }

        internal bool RecognizePlanByEarleyParser(List<Term> plan, List<Action> planPrefix, List<Term> initialState, List<Rule> rules, 
            out Rule finalRule, out Subplan finalSubtask, out List<int> addedActionsByIteration, CancellationToken cancellationToken, 
            EarleyStateHeuristic heuristic = null)
        {
            List<Rule> rulesExpandedByAllPossibleSubtaskOrderings = ExpandExplicitSubtaskOrdering(rules);
            CreateConstantTypeInstances(AllConstants, AllConstantTypes);

            if (!Init(plan, AllTaskTypes, AllActionTypes, AllConstants, initialState))
            {
                finalRule = null;
                finalSubtask = null;
                addedActionsByIteration = null;
                return false;
            }

            Subplan subplan;

            if (heuristic == null)
            {
                subplan = RunEarleyParsingAsPlanRecognition(planPrefix, AllActionTypes, rulesExpandedByAllPossibleSubtaskOrderings, AllTaskTypes, 
                    cancellationToken);
            }
            else
            {
                subplan = RunEarleyParsingAsPlanRecognitionWithHeuristic(planPrefix, AllActionTypes, rulesExpandedByAllPossibleSubtaskOrderings, 
                    AllTaskTypes, heuristic, cancellationToken);
            }

            if (cancellationToken.IsCancellationRequested)
            {
                finalRule = null;
                finalSubtask = null;
                addedActionsByIteration = null;
                return false;
            }

            addedActionsByIteration = new List<int>(); // irrelevant here
            finalSubtask = subplan;
            finalRule = subplan.LastRuleInstance.Rule; 
            return true;
        }

        public void ComputeSupports()
        {
            COMPUTING_SUPPORTS = true;
        }
    }
}
