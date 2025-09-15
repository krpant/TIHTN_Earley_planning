using System;
using System.Collections.Generic;
using System.Linq;

namespace PlanRecognitionNETF
{
    /// <summary>
    /// Type of tasks/subplans.
    /// 
    /// </summary>
    class TaskType
    {
        /// <summary>
        /// List of rules that contains this type of task. 
        /// </summary>
        public List<Rule> Rules;
        public String Name; //Task name
        public int NumOfVariables; //Number of variables. So that load(X,Y) and load(X,Y,Z) are different TaskTypes
        public List<Subplan> Instances;
        public int minTasklength; //This is set to fixed 100000.

        public Term TaskTerm; 

        public TaskType(String name, int numOfVars)
        {
            this.Name = name;
            this.NumOfVariables = numOfVars;
            this.Instances = new List<Subplan>();
            this.Rules = new List<Rule>();
            minTasklength = 100000;
        }

        public TaskType(String name, int numOfVars, List<Subplan> instances, List<Rule> rules)
        {
            this.Rules = rules;
            this.Instances = instances;
            this.Name = name;
            this.NumOfVariables = numOfVars;
            minTasklength = 100000;
        }

        /// <summary>
        /// Sets mintask length to i if i is smaller than mintask length otherwise does nothing.
        /// Return true if value changed.
        /// </summary>
        /// <param name="i"></param>
        public bool SetMinTaskLengthIfSmaller(int i)
        {
            if (i < minTasklength)
            {
                minTasklength = i;
                return true;
            }
            return false;
        }


        public void AddInstance(Subplan t)
        {
            if (!Instances.Contains(t)) Instances.Add(t);
        }

        /// <summary>
        /// Tells the rule that this task is now ready. If the rule is full (all tasks are ready it returns it otherwise returns null)
        /// </summary>
        /// <returns></returns>
        private Rule ActivateRule(Rule r, int i, int iteration)
        {
            bool fullyActivated = r.Activate(this, i, iteration);
            if (fullyActivated) return r;
            else return null;
        }
        /// <summary>
        /// Tells the rules that this task is now ready. If the rules are full (all tasks are ready it returns them otherwise returns empty list)
        /// What if this tasktype is in the rule multiple times. Solution check as ready as long as you have enough instances. If zou have 5 instances zou can fulfil the rule up to five times. 
        /// Tady by stacilo mit ten rule jen jednou. 
        /// </summary>
        /// <returns></returns>
        public List<Rule> ActivateRules(int iteration)
        {
            int instancesCount = Instances.Count;
            List<Rule> rulesReadyToGo = new List<Rule>();
            foreach (Rule r in Rules)
            {
                Rule r2 = ActivateRule(r, instancesCount, iteration);
                if (r2 != null) rulesReadyToGo.Add(r2);

            }
            rulesReadyToGo = rulesReadyToGo.Distinct().ToList();
            return rulesReadyToGo;

        }

        public void AddRule(Rule r)
        {
            this.Rules.Add(r);
        }

        public override string ToString()
        {
            string text = string.Join(",", Rules.Select(x => x.MainTaskType.Name));
            string text2 = string.Join(",", Instances.Select(x => x.TaskInstance.Name));
            String s = "TaskType:" + this.Name + " Num of Variables " + NumOfVariables + " Rules: " + text + " Instances: " + text2;
            return s;
        }

        public override bool Equals(object obj)
        {
            return obj is TaskType type &&
                   Name == type.Name &&
                   NumOfVariables == type.NumOfVariables;
        }

        public override int GetHashCode()
        {
            int hashCode = 932716889;
            hashCode = hashCode * -1521134295 + Name.GetHashCode();
            hashCode = hashCode * -1521134295 + NumOfVariables.GetHashCode();
            return hashCode;
        }
    }
}
