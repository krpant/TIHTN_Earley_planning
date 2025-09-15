using System;
using System.Linq;

namespace PlanRecognitionNETF
{
    /// <summary>
    /// This is just a name and variable. 
    /// This is used almost everywhere. It is used as a name of subplans,actions even conditions.
    /// </summary>
    class Term
    {
        public String Name { get; private set; }
        public Constant[] Variables { get; private set; }

        public Term(String name, Constant[] variables)
        {
            Name = name;
            Variables = variables;
        }

        public Term(String name, int i)
        {
            Name = name;
            Variables = new Constant[i];
        }

        public override bool Equals(object obj)
        {
            if (obj == null || GetType() != obj.GetType())
            {
                return false;
            }
            Term cond2 = obj as Term;
            if (Name.Equals(cond2.Name))
            {
                for (int i = 0; i < cond2.Variables.Length; i++)
                {
                    if (Variables[i] != null && cond2.Variables[i] != null)
                    {
                        if (!Variables[i].Equals(cond2.Variables[i])) return false;
                    }
                }
                return true;
            }
            else return false;

        }

        public bool SameType(Term t)
        {
            return (this.Name.Equals(t.Name) && this.Variables.Length == t.Variables.Length);
        }
        public override int GetHashCode()
        {
            int hash = 17;
            hash = hash * 23 + Name.GetHashCode();
            foreach (Constant s in Variables)
            {
                hash = hash * 23 + s.GetHashCode();
            }
            return hash;
        }

        public override string ToString()
        {
            string s = $"{Name}(";
            for (int i = 0; i < Variables.Length; i++)
            {
                if (i != 0)
                {
                    s += ", ";
                }
                s += Variables[i].Name;
            }

            return s + ")";
        }

        //Returns true if two terms are equal in every variable except the one where there is null. 
        //Allows different lengths. 
        public bool EqualOrNull(Term t)
        {
            if (t.Name != this.Name) return false;
            int maxCount = Math.Max(this.Variables.Count(), t.Variables.Count());
            for (int i = 0; i < maxCount; i++)
            {
                if (i >= this.Variables.Count() || i >= t.Variables.Count()) return true;
                if (this.Variables[i] != null && t.Variables[i] != null)
                {
                    if (this.Variables[i] != t.Variables[i]) return false;
                }
            }
            return true;
        }


        //Handles logical equality conditions. 
        public bool CheckEquality(bool pos)
        {
            int i = 0;
            foreach (Constant var in this.Variables)
            {
                if (pos)
                {
                    foreach (Constant var2 in this.Variables)
                    {
                        if (!var.Equals(var2)) return false;
                    }
                }
                else
                {
                    for (int j = 0; j < this.Variables.Length; j++)
                    {
                        if (j != i)
                        {
                            if (var == this.Variables[j]) return false;
                        }
                    }
                }
                i++;
            }
            return true;
        }
    }
}
