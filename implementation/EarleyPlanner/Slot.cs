using System;
using System.Collections.Generic;
using System.Linq;

namespace PlanRecognitionNETF
{
    /// <summary>
    /// Represnets one point in a timeline. 
    /// It has an action and positive and negative preconditions and effects. 
    /// </summary>
    class Slot
    {
        public List<Term> PosPreConditions;
        public List<Term> NegPreConditions;
        public Term a;
        public List<Term> PosPostConditions;
        public List<Term> NegPostConditions;

        public Slot()
        {
            PosPreConditions = new List<Term>();
            NegPreConditions = new List<Term>();
            PosPostConditions = new List<Term>();
            NegPostConditions = new List<Term>();
        }

        public Slot(Slot s)
        {
            if (s.a != null) this.a = s.a;
            this.PosPreConditions = s.PosPreConditions;
            this.NegPreConditions = s.NegPreConditions;
            this.PosPostConditions = s.PosPostConditions;
            this.NegPostConditions = s.NegPostConditions;
        }

        public Slot(Term a) : base()
        {
            this.a = a;
        }

        /// <summary>
        /// Checks whether any of it's conditions are in conflict. If not returns true.
        /// </summary>
        public bool IsValid()
        {
            return !ContainsSameElements(PosPreConditions, NegPreConditions) 
                && !ContainsSameElements(PosPostConditions, NegPostConditions);
        }

        /// <summary>
        /// Returns true if both lists contain at least one same element. 
        /// </summary>
        /// <param name="c1"></param>
        /// <param name="c2"></param>
        /// <returns></returns>
        public bool ContainsSameElements(List<Term> c1, List<Term> c2)
        {
            foreach (Term c in c1)
            {
                if (c2.Contains(c)) 
                    return true;
            }
            return false;
        }

        public override string ToString() 
        {
            string text3 = string.Join(",", PosPreConditions.Select(x => x.ToString()));
            string text4 = string.Join(",", NegPreConditions.Select(x => x.ToString()));
            string text5 = string.Join(",", PosPostConditions.Select(x => x.ToString()));
            string text6 = string.Join(",", NegPostConditions.Select(x => x.ToString()));
            String s = "Slot: " + a;
            return s;
        }

    }
}
