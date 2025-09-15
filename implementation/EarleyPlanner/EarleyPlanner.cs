using PlanRecognitionNETF;
using System.Collections.Generic;
using System.Linq;

namespace PlanRecognitionExtension
{
    internal class EarleyPlanner : PartialObservabilityEarleyParser
    {
        readonly List<Task> toGoals; // totally ordered abstract tasks from the initial HTN

        public EarleyPlanner(List<TaskType> allTaskTypes, List<ActionType> allActionTypes, List<Constant> allConstants, 
            List<ConstantType> allConstantTypes, List<Term> initialState, List<Task> toGoals, bool actionInsertionAllowed = true, 
            bool actionDeletionAllowed = false, bool anytimeGoals = true, bool returnFirstResult = false) : base(allTaskTypes, allActionTypes, allConstants, 
                allConstantTypes, initialState, actionInsertionAllowed, actionDeletionAllowed, anytimeGoals, returnFirstResult)
        {
            this.toGoals = toGoals;
            ALLOW_DELETING_ACTIONS = false;
            ALLOW_INSERTING_NEW_ACTIONS = true;
        }

        protected override PriorityQueueWatchingFlaws InitQueue(List<TaskType> allTaskTypes, out AbstractTask dummyStartingTask, List<Rule> allRules, List<HashSet<QueueItem>> completedStatesByFirstAction, List<HashSet<QueueItem>> partiallyProcessedStatesByLastAction, List<Action> plan)
        {
            PriorityQueueWatchingFlaws queue = new();
            TaskType dummyStartingTaskType = new("start_dummy", 0);
            AllDummyTaskTypes = new()
            {
                dummyStartingTaskType
            };
            dummyStartingTask = new AbstractTask(new Task(dummyStartingTaskType));

            List<int>[] arrayOfReferenceLists = new List<int>[toGoals.Count];

            int varIndex = 0;
            for (int i = 0; i < toGoals.Count; i++)
            {
                Task g = toGoals[i];
                List<int> referenceList = Enumerable.Range(varIndex, g.TaskType.NumOfVariables).ToList();
                varIndex += referenceList.Count;
                arrayOfReferenceLists[i] = referenceList;
            }

            Rule dummyRule = new()
            {
                MainTaskType = dummyStartingTaskType,
                TaskTypeArray = toGoals.Select(x => x.TaskType).ToArray(),
                ArrayOfReferenceLists = arrayOfReferenceLists,
                MainTaskReferences = new List<int>(0)
            };

            CFGTask[] cFGSubtasks = toGoals.Select(x => new AbstractTask(x) as CFGTask).ToArray();
            CFGRule dummyCFGRule = new(dummyStartingTask, cFGSubtasks, dummyRule, this);
            QueueItem queueItem = QueueItem.CreateQueueItemAndAddToTables(dummyCFGRule, 0, 0, completedStatesByFirstAction,
                partiallyProcessedStatesByLastAction, plan, this);
            queue.Enqueue(queueItem);
            return queue;
        }

        protected override void WriteSolution(Subplan bestGoalSoFar, List<ActionSubplan> bestPlanSoFar)
        {
            EntryPoint.WritePlannerSolution(bestPlanSoFar);
        }

        protected override Subplan GoalTask(List<Subplan> groundedSubtasks)
        {
            TaskType dummyRootTask = new("root", groundedSubtasks.Select(x => x.TaskType.NumOfVariables).Sum());
            Constant[] variables = groundedSubtasks.SelectMany(x => x.TaskInstance.Variables).ToArray();
            List<Slot> timeline = groundedSubtasks.SelectMany(x => x.Timeline).ToList();
            Subplan subplan = new(new Term(dummyRootTask.Name, variables), 0, timeline.Count - 1, dummyRootTask);
            subplan.Timeline = timeline;
            subplan.usedActions = Enumerable.Repeat(true, timeline.Count).ToArray();
            subplan.LastRuleInstance = new RuleInstance(subplan, groundedSubtasks,
            new Rule
            {
                Name = "dummyRootRule"
            }, variables.Select(x => x.Name).ToList(), variables.ToList());
            foreach (var subtask in groundedSubtasks)
            {
                foreach (var ruleInstance in subtask.History)
                {
                    subplan.AddToHistory(ruleInstance);
                }
            }
            return subplan;
        }

        internal override int ComputeNumberOfFlaws(Subplan subplan)
        {
            return subplan.usedActions.Count(x => x);
        }
    }

}
