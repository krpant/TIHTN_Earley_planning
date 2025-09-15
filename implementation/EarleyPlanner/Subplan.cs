using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace PlanRecognitionNETF
{
    /// <summary>
    /// Represents a task and its timeline.
    /// </summary>
    class Subplan
    {
        /// <summary>
        /// The name and avriables of this subplan. 
        /// </summary>
        public Term TaskInstance;
        public double StartIndex;
        public double EndIndex;
        public List<Slot> Timeline;
        public int Iteration; //Iteration at which it was created. 
        public bool[] usedActions; //Is set to true if action on that slot is used. The whole array has plan size of creation. 
        public HashSet<RuleInstance> History { get; private set; } = new HashSet<RuleInstance>(new RuleInstanceStringComparer());
        public RuleInstance LastRuleInstance { get; set; }

        public static string DUMMY_EMPTY_ACTION_NAME = "empty_rule_slot";

        public int IndexInCurrentPlan { get; set; } = -1; // necessary for TIHTN

        class RuleInstanceStringComparer : EqualityComparer<RuleInstance>
        {
            public override bool Equals(RuleInstance x, RuleInstance y)
            {
                return x.ToString() == y.ToString();
            }

            public override int GetHashCode(RuleInstance obj)
            {
                return obj.ToString().GetHashCode();
            }
        }

        internal Subplan Copy()
        {
            Subplan subplan = new(this);
            subplan.Timeline.AddRange(Timeline);
            if (usedActions == null)
            {
                usedActions = new bool[0];
            }
            subplan.usedActions = new bool[usedActions.Length];
            usedActions.CopyTo(subplan.usedActions, 0);
            subplan.Iteration = Iteration;
            subplan.History = new HashSet<RuleInstance>(History); 
            subplan.LastRuleInstance = LastRuleInstance;
            subplan.StartIndex = StartIndex;
            subplan.EndIndex = EndIndex;
            return subplan;
        }

        public TaskType TaskType { get; private set; }


        public Subplan(Subplan t)
        {
            this.TaskInstance = t.TaskInstance;
            this.TaskType = t.TaskType;
            Timeline = new List<Slot>();
        }

        public Subplan(Term a, double start, double end, TaskType taskType)
        {
            this.TaskInstance = a;
            this.StartIndex = start;
            this.EndIndex = end;
            TaskType = taskType;
            Timeline = new Slot[(int)(Math.Ceiling(end) - Math.Ceiling(start) + 1)].ToList();
        }

        /// <summary>
        /// Creates bool array with used actions. 
        /// </summary>
        /// <param name="s"></param>
        internal void CreateUsedActions(List<Subplan> s)
        {
            bool[] longestArray = s.OrderBy(x => x.usedActions != null ? x.usedActions.Length : 0).Last().usedActions; // if it is null it gives value 0
            if (longestArray != null) usedActions = new bool[longestArray.Length];
            foreach (Subplan subplan in s)
            {
                if (subplan.usedActions != null)
                {
                    for (int i = 0; i < subplan.usedActions.Length; i++)
                    {
                        if (subplan.usedActions[i]) usedActions[i] = true;
                    }
                }
            }

        }

        /// <summary>
        /// Adds this task to instances of this task type and returns the task type
        /// </summary>
        /// <returns></returns>
        internal void AddToTaskType()
        {
            this.TaskType.AddInstance(this);
        }

        /// <summary>
        /// Returns i-th slot in order.
        /// Returns counting slots from 0 so even if the whole subplans atsrta at position 5 this can still be zero. 
        /// </summary>
        /// <param name="i"></param>
        /// <returns></returns>
        public Slot GetSlot(double i) //check if this works with making megaslots. 
        {
            int j = (int)Math.Round(i);
            return Timeline[j];

        }
        /// <summary>
        /// Sets i-th Slot to slot s. If i-th slot does not exist does nothing. 
        /// </summary>
        /// <param name="i"></param>
        /// <param name="s"></param>
        public void SetSlot(double i, Slot s)
        {
            int j = (int)Math.Round(i);
            Timeline[j] = s;
        }

        internal double GetEndIndex()
        {
            return EndIndex;
        }

        internal double GetStartIndex()
        {
            return StartIndex;
        }

        public override string ToString()
        {

            return TaskInstance.ToString();
        }

        public string GetPlanString()
        {
            StringBuilder sb = new StringBuilder();
            bool firstAction = true;
            foreach (var a in Timeline)
            {
                if (a.a != null)
                {
                    if (!firstAction)
                    {
                        sb.Append(", ");
                    }
                    firstAction = false;
                    sb.Append(a.a.Name);
                    sb.Append("(");
                    bool firstVar = true;
                    foreach (var v in a.a.Variables)
                    {
                        if (!firstVar)
                        {
                            sb.Append(", ");
                        }
                        firstVar = false;
                        sb.Append(v.Name);
                    }
                    sb.Append(")");
                }
            }
            return sb.ToString();
        }

        public void WritePlan() 
        {
            int length = 0;
            int i = 0;
            string s = "";
            foreach (var a in Timeline)
            {
                if (a.a != null && a.a.Name != DUMMY_EMPTY_ACTION_NAME)
                {
                    ++length;
                    s += i + ": ";
                    i++;
                    s += a.a.Name + "(";
                    bool first = true;
                    foreach (var v in a.a.Variables)
                    {
                        if (!first)
                        {
                            s += ", ";
                        }
                        first = false;
                        s += v.Name;
                    }
                    s += ")\n";
                }
            }
            Console.WriteLine("Plan length: " + length + "\nPlan:\n" + s);
        }

        internal string ActionString(int index)
        {
            string s = "";
            Slot a = Timeline[index];

            while (a.a == null || a.a.Name == DUMMY_EMPTY_ACTION_NAME)
            {
                a = Timeline[++index];
            }

                s += a.a.Name + "(";
                bool first = true;
                foreach (var v in a.a.Variables)
                {
                    if (!first)
                    {
                        s += ", ";
                    }
                    first = false;
                    s += v.Name;
                }
                s += ")";

            return s;


        }
        
        public void WriteAction()
        {
            string text = string.Join(", ", Timeline.Select(x => x.a));
            Console.WriteLine(text);
        }

        internal void AddToHistory(RuleInstance ruleInstance)
        {
            History.Add(new RuleInstance(ruleInstance.MainTask, new List<Subplan>(ruleInstance.Subtasks), ruleInstance.Rule,
                ruleInstance.AllVars, ruleInstance.AllConstants));
            LastRuleInstance = ruleInstance;
        }

        internal void WriteHistory()
        {
            Console.WriteLine("History:");
            HashSet<string> used = new HashSet<string>();
            foreach (var r in History)
            {
                
                string s = r.GetRuleInstanceString();
                if (!used.Contains(s))
                {
                    Console.WriteLine("\t" + s + $" ({r.Rule.Name})");
                    used.Add(s);
                }
            }
        }

        internal int PlanLength()
        {
            return Timeline.Count((x) => (x.a != null && x.a.Name != DUMMY_EMPTY_ACTION_NAME)); 
        }
    }
}
