using System;
using System.Collections.Generic;
using System.Linq;

namespace PlanRecognitionNETF
{
    /// <summary>
    /// Actions are only used within the program to create new tasks. At the start to create tasks corresponding to plan and then in recognition when we add new actions.     /// 
    /// </summary>
    /// 
    class ActionType
    {
        public Term ActionTerm;
        /// <summary>
        /// String is the name of the action and the list represents references to variables in the main action. For exmaple for condition at(C,L1) for load(C,L1,R)  we
        /// have tuple (at,(0,1))
        /// </summary>
        public List<Tuple<String, List<int>>> PosPreConditions;
        public List<Tuple<String, List<int>>> NegPreConditions;
        public List<Tuple<String, List<int>>> PosPostConditions; //effects
        public List<Tuple<String, List<int>>> NegPostConditions;//effects
        public List<Term> Instances;
        public TaskType TaskType;

        public ActionType()
        {
            PosPreConditions = new List<Tuple<string, List<int>>>();
            NegPreConditions = new List<Tuple<string, List<int>>>();
            PosPostConditions = new List<Tuple<string, List<int>>>();
            NegPostConditions = new List<Tuple<string, List<int>>>();
            Instances = new List<Term>();
        }

        public override bool Equals(object obj)
        {
            return obj is ActionType type &&
                   ActionTerm.Equals(type.ActionTerm); 
        }

        public override int GetHashCode()
        {
            return -1463861235 + ActionTerm.GetHashCode();
        }

        public override string ToString()
        {
            string text2 = string.Join(",", PosPreConditions.Select(x => x.Item1));
            string text3 = string.Join(",", NegPreConditions.Select(x => x.Item1));
            string text4 = string.Join(",", PosPostConditions.Select(x => x.Item1));
            string text5 = string.Join(",", NegPostConditions.Select(x => x.Item1));
            string textTask = "Unknown";
            if (TaskType != null) textTask = TaskType.Name;
            String s = ActionTerm.ToString() + " TaskType:" + textTask + " posPreCond" + text2 + "negPreCond " + text3 + "posPostCond " + text4 + " negPostCond " + text5;
            return s;
        }
    }
}
