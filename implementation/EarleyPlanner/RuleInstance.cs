using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;

namespace PlanRecognitionNETF
{
    /// <summary>
    /// This is essential a method/rule with all variables and subtasks filled. 
    /// This creates proper conditions. Currently conditions are just name with number reference we want actual conditions with strings. 
    /// </summary>
    class RuleInstance
    {
        public Subplan MainTask;
        public List<Subplan> Subtasks;
        public Rule Rule { get; }
        /// <summary>
        /// Term is the condition and the int says to which subtask is this related to. (Counted from 0)
        /// </summary>
        public List<Tuple<int, Term>> PosPreConditions { get; private set; }
        public List<Tuple<int, Term>> NegPreConditions { get; private set; }
        public List<Tuple<int, Term>> PosPostConditions { get; private set; }
        public List<Tuple<int, Term>> NegPostConditions { get; private set; }
        public List<Tuple<int, int, Term>> PosBetweenConditions { get; private set; }
        public List<Tuple<int, int, Term>> NegBetweenConditions { get; private set; }
        bool valid;
        internal List<String> AllVars { get; private set; } 
        internal List<Constant> AllConstants { get; private set; } 

        // Both necessary for TIHTN planning:
        public int FirstIndexInCurrentPlan { get; private set; } // includes actions inserted to satisfy rule preconditions
        public int LastIndexInCurrentPlan { get; private set; }

        public RuleInstance(Subplan mainTask, List<Subplan> subtasks, Rule rule, List<String> allVars, List<Constant> allconstants)
        {
            this.MainTask = mainTask;
            this.Subtasks = subtasks;
            valid = CheckOrdering(rule.orderConditions);
            PosPreConditions = new List<Tuple<int, Term>>();
            NegPreConditions = new List<Tuple<int, Term>>();
            PosPostConditions = new List<Tuple<int, Term>>();
            NegPostConditions = new List<Tuple<int, Term>>();
            PosBetweenConditions = new List<Tuple<int, int, Term>>();
            NegBetweenConditions = new List<Tuple<int, int, Term>>();
            if (valid) valid = CreateConditions(rule.posBetweenConditions, PosBetweenConditions, allVars, rule.AllVarsTypes); //These go first as they are most likely to break the rule instance
            if (valid) valid = CreateConditions(rule.negBetweenConditions, PosBetweenConditions, allVars, rule.AllVarsTypes);
            if (valid) valid = CreateConditions(rule.posPreConditions, PosPreConditions, allVars, rule.AllVarsTypes, true, allconstants);
            if (valid) valid = CreateConditions(rule.negPreConditions, NegPreConditions, allVars, rule.AllVarsTypes, false, allconstants);
            if (valid) valid = CreateConditions(rule.posPostConditions, PosPostConditions, allVars, rule.AllVarsTypes, true, allconstants);
            if (valid) valid = CreateConditions(rule.negPostConditions, NegPostConditions, allVars, rule.AllVarsTypes, false, allconstants);
            Rule = rule;
            this.AllVars = allVars;
            AllConstants = allconstants;

            FindIndexesOfActionsInCurrentPlan();
        }

        private void FindIndexesOfActionsInCurrentPlan()
        {
            if (Subtasks[0].LastRuleInstance == null)
            {
                FirstIndexInCurrentPlan = Subtasks[0].IndexInCurrentPlan;
            }
            else
            {
                FirstIndexInCurrentPlan = Subtasks[0].LastRuleInstance.FirstIndexInCurrentPlan;
            }

            if (Subtasks[^1].LastRuleInstance == null)
            {
                LastIndexInCurrentPlan = Subtasks[^1].IndexInCurrentPlan;
            }
            else
            {
                LastIndexInCurrentPlan = Subtasks[^1].LastRuleInstance.LastIndexInCurrentPlan;
            }

            Debug.Assert(FirstIndexInCurrentPlan >= 0);
            Debug.Assert(LastIndexInCurrentPlan >= 0);
            Debug.Assert(FirstIndexInCurrentPlan <= LastIndexInCurrentPlan);
        }

        public bool IsValid()
        {
            return valid;
        }

        /// <summary>
        /// Checks whether subtasks are properly ordered. 
        /// </summary>
        /// <param name="orderConditions"></param>
        /// <returns></returns>
        private bool CheckOrdering(List<Tuple<int, int>> orderConditions)
        {
            if (orderConditions == null || !orderConditions.Any()) return true; //If there is no ordering than it's ordered properly.
            foreach (Tuple<int, int> combo in orderConditions)
            {
                Subplan subtask1 = Subtasks[combo.Item1];
                Subplan subtask2 = Subtasks[combo.Item2];
                if (!(subtask1.GetEndIndex() <= subtask2.GetStartIndex())) return false; //If tasks are interleaving then there can't be order between them. 
            }
            return true;
        }
        /// <summary>
        /// Creates proper condition with string from a numbered reference. 
        /// Also solves equality conditions as we don't add them to nromal conditions but instead check them immediately. 
        /// </summary>
        /// <param name="PostConditions1"></param>
        /// <param name="PostConditions2"></param>
        /// <param name="allVars"></param>
        /// <param name="allVarsType"></param>
        /// <param name="pos"></param>
        /// <param name="allconstants"></param>
        /// <returns></returns>
        private bool CreateConditions(List<Tuple<int, string, List<int>>> PostConditions1, List<Tuple<int, Term>> PostConditions2, List<String> allVars, List<ConstantType> allVarsType, bool pos, List<Constant> allconstants)
        {
            bool valid = true;
            bool containsForallCondition = false;
            foreach (Tuple<int, string, List<int>> conditionTuple in PostConditions1)
            {
                Constant[] newVars = new Constant[conditionTuple.Item3.Count];
                for (int i = 0; i < conditionTuple.Item3.Count; i++)
                {
                    int num = conditionTuple.Item3[i];
                    if (num < 0 || num >= allVars.Count) return false;
                    newVars[i] = new Constant(allVars[num], allVarsType[num]);
                    if (allVars[num].StartsWith("!"))
                    {
                        //This is an forall variable. 
                        //So I must create many instances of this condition. With each constant of desired type. 
                        containsForallCondition = true;
                    }
                }
                Term condition = new Term(conditionTuple.Item2, newVars);
                if (conditionTuple.Item2.Contains("equal") || conditionTuple.Item2.Equals("=")) valid = condition.CheckEquality(pos);
                else
                { //We do not add equality conditions to normal conditions. 
                    if (containsForallCondition)
                    {
                        PostConditions2.AddRange(CreateForAllConditions(newVars, allconstants, allVarsType, conditionTuple.Item1, conditionTuple.Item2));
                    }
                    else
                    {
                        Tuple<int, Term> tuple = new Tuple<int, Term>(conditionTuple.Item1, condition);
                        PostConditions2.Add(tuple);
                    }
                }
                containsForallCondition = false;
            }
            return true;
        }

        /// <summary>
        /// Creates proper instance of forall condition. 
        /// </summary>
        /// <param name="newVars"></param>
        /// <param name="allconstants"></param>
        /// <param name="allVarsType"></param>
        /// <param name="subtaskNum"></param>
        /// <param name="name"></param>
        /// <returns></returns>
        private List<Tuple<int, Term>> CreateForAllConditions(Constant[] newVars, List<Constant> allconstants, List<ConstantType> allVarsType, int subtaskNum, string name)
        {
            List<Tuple<int, Term>> solution = new List<Tuple<int, Term>>();
            for (int i = 0; i < newVars.Count(); i++)
            {
                if (newVars[i].Name.StartsWith("!"))
                {
                    List<Constant> rightTypeConstants = allconstants.Where(x => newVars[i].Type.IsAncestorTo(x.Type)).ToList();
                    foreach (Constant c in rightTypeConstants)
                    {
                        newVars[i] = c;
                        Term condition = new Term(name, newVars.ToArray());
                        Tuple<int, Term> tuple = new Tuple<int, Term>(subtaskNum, condition);
                        solution.Add(tuple);
                    }
                }
            }
            return solution;
        }

        /// <summary>
        /// Creates proper between condtiions. 
        /// </summary>
        /// <param name="BetweenConditions1"></param>
        /// <param name="BetweenConditions2"></param>
        /// <param name="allVars"></param>
        /// <param name="allVarsType"></param>
        /// <returns></returns>
        private bool CreateConditions(List<Tuple<int, int, string, List<int>>> BetweenConditions1, List<Tuple<int, int, Term>> BetweenConditions2, List<String> allVars, List<ConstantType> allVarsType)
        {
            //Also check if this works with constants
            foreach (Tuple<int, int, string, List<int>> conditionTuple in BetweenConditions1)
            {
                Subplan task1 = Subtasks[conditionTuple.Item1];
                Subplan task2 = Subtasks[conditionTuple.Item2];
                Constant[] newVars = new Constant[conditionTuple.Item4.Count];
                for (int i = 0; i < conditionTuple.Item4.Count; i++)
                {
                    int num = conditionTuple.Item4[i];
                    if (num < 0 || num >= allVars.Count) return false;
                    newVars[i] = new Constant(allVars[num], allVarsType[num]);
                }
                Term condition = new Term(conditionTuple.Item3, newVars);
                Tuple<int, int, Term> tuple = new Tuple<int, int, Term>(conditionTuple.Item1, conditionTuple.Item2, condition);
                BetweenConditions2.Add(tuple);
            }
            return true;

        }

        public string GetRuleInstanceString() 
        {
            string s = MainTask.TaskInstance.Name + "(";
            bool first = true;
            foreach (var v in MainTask.TaskInstance.Variables)
            {
                if (!first)
                {
                    s += ", ";
                }
                else
                {
                    first = false;
                }
                s += v.Name;
            }
            s += ") -> ";

            first = true;
            foreach (var t in Subtasks)
            {
                if (!first)
                {
                    s += ", ";
                }
                else
                {
                    first = false;
                }
                s += t.TaskInstance.Name + "(";
                bool firstVar = true;
                foreach (var v in t.TaskInstance.Variables)
                {
                    if (!firstVar)
                    {
                        s += ", ";
                    }
                    else
                    {
                        firstVar = false;
                    }
                    s += v.Name;
                }
                s += ")";
            }
            return s + "; all variables: " + AllVariablesString();
        }

        string AllVariablesString()
        {
            if (AllVars == null || AllVars.Count == 0)
            {
                return "";
            }
            string s = AllVars[0];

            for (int i = 1; i < AllVars.Count; i++) 
            {
                s += ", " + AllVars[i];
            }
            return s;
        }

        public override string ToString()
        {
            return Rule.Name + ": " + GetRuleInstanceString();
            
            
            string text = string.Join(",", Subtasks.Select(x => x.TaskInstance.Name));
            string text2 = string.Join(",", PosPreConditions.Select(x => x.Item2.Name));
            string text3 = string.Join(",", NegPreConditions.Select(x => x.Item2.Name));
            string text4 = string.Join(",", PosPostConditions.Select(x => x.Item2.Name));
            string text5 = string.Join(",", NegPostConditions.Select(x => x.Item2.Name));
            string text6 = string.Join(",", PosBetweenConditions.Select(x => x.Item3.Name));
            string text7 = string.Join(",", NegBetweenConditions.Select(x => x.Item3.Name));
            String s = "RuleInstance: " + this.MainTask.TaskInstance.Name + " subtasks " + text + " posPreCond" + text2 + "negPreCond " + text3 + "posPostCond " + text4 + " negPostCond " + text5 + "posBetweenCond " + text6 + "negBetweenCond" + text7;
            return s;
        }
    }
}
