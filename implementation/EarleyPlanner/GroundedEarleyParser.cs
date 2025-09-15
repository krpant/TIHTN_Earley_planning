using PlanRecognitionNETF;
using System;
using System.Collections.Generic;
using System.Threading;

namespace PlanRecognitionExtension
{
    internal class GroundedEarleyParser : EarleyParser
    {
        List<Dictionary<CFGTask, HashSet<QueueItem>>> tableByNextTask;
        Dictionary<TaskType, List<Rule>> rulesByMainTask;

        public GroundedEarleyParser(List<TaskType> allTaskTypes, List<ActionType> allActionTypes, List<Constant> allConstants, 
            List<ConstantType> allConstantTypes, List<Term> initialState)
            : base(allTaskTypes, allActionTypes, allConstants, allConstantTypes, initialState)
        {
        }

        internal override bool VerifyPlanByEarleyParser(List<Term> plan, List<Action> planPrefix, List<Term> initialState, List<Rule> rules,
            out Rule finalRule, out Subplan finalSubtask, out List<int> addedActionsByIteration, CancellationToken cancellationToken, Task rootTask = null, EarleyStateHeuristic heuristic = null)
        {
            SetTable(planPrefix);
            SetRulesByMainTask(rules);
            return base.VerifyPlanByEarleyParser(plan, planPrefix, initialState, rules, out finalRule, out finalSubtask, out addedActionsByIteration, cancellationToken, rootTask, heuristic);
        }

        protected override void AddToRules(List<Rule> allRulesExtended, Rule rule)
        {
            base.AddToRules(allRulesExtended, rule);

            if (!rulesByMainTask.TryGetValue(rule.MainTaskType, out List<Rule> list))
            {
                list = new List<Rule>();
                rulesByMainTask[rule.MainTaskType] = list;
            }
            list.Add(rule);
        }

        void SetTable(List<Action> planPrefix)
        {
            tableByNextTask = new(planPrefix.Count + 2);
            for (int i = 0; i <= planPrefix.Count + 1; i++)
            {
                tableByNextTask.Add(new());
            }
        }

        void SetRulesByMainTask(List<Rule> rules)
        {
            rulesByMainTask = new();

            foreach (var rule in rules)
            {
                if (!rulesByMainTask.TryGetValue(rule.MainTaskType, out List<Rule> list))
                {
                    list = new List<Rule>();
                    rulesByMainTask[rule.MainTaskType] = list;
                }
                list.Add(rule);
            }
        }

        void AddToTableByNextTask(int iterationIndex, QueueItem queueItem)
        {
            if (queueItem.CFGRule.TryGetNextTask(out CFGTask nextTask))
            {
                if (!tableByNextTask[iterationIndex].TryGetValue(nextTask, out HashSet<QueueItem> set))
                {
                    set = new HashSet<QueueItem>();
                    tableByNextTask[iterationIndex][nextTask] = set;
                }
                set.Add(queueItem);
            }
        }

        protected override void AddToTable(int i, QueueItem item, List<HashSet<QueueItem>> table)
        {
            base.AddToTable(i, item, table);
            AddToTableByNextTask(i, item);
        }

        protected override IEnumerable<QueueItem> EnumerateTableItems(int iterationIndex, List<HashSet<QueueItem>> table, 
            CFGTask mainTask)
        {
            if (tableByNextTask[iterationIndex].ContainsKey(mainTask))
            {
                foreach (var item in tableByNextTask[iterationIndex][mainTask])
                {
                    yield return item;
                }
            }
            else
            {
#if DEBUG
                foreach (var key in tableByNextTask[iterationIndex].Keys)
                {
                    Console.WriteLine($"\t{mainTask} == {key}: {mainTask.Equals(key)}");
                }
#endif
            }
        }

        protected override void AddNewTableColumn(List<HashSet<QueueItem>> table)
        {
            base.AddNewTableColumn(table);
            tableByNextTask.Add(new());
        }

        protected override IEnumerable<Rule> EnumerateRulesByMainTask(List<Rule> allRules, TaskType desiredTaskType)
        {
            foreach (var rule in rulesByMainTask[desiredTaskType])
            {
                yield return rule;
            }
        }
    }
}
