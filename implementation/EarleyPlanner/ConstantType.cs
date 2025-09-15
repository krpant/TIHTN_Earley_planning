using System;
using System.Collections.Generic;

namespace PlanRecognitionNETF
{
    /// <summary>
    /// We will have a list of global constant types and to them we refer from the constants. 
    /// </summary>
    class ConstantType
    {
        public String Name;
        public List<ConstantType> AncestorTypes { get; private set; } //must also always contain the task itself. //Deep all ancestors
        List<ConstantType> Children;// never contains itself. //Shallow just one line of children. 
        public List<Constant> Instances { private set; get; }
        public List<ConstantType> DescendantTypes { private set; get; } //Deep and contains itself. 

        internal void AddInstance(Constant constant)
        {
            if (!Instances.Contains(constant)) this.Instances.Add(constant);
        }


        /// <summary>
        /// Ads c as its ancestor. Then calls all its children and they add c as their ancestor too.
        /// Checks if c is not its child, because then we would have a cycle, which we don't allow. 
        /// Does not add itself as a child to the ancestor that must be done separately. 
        /// </summary>
        /// <param name="c"></param>
        public void AddAncestor(ConstantType c)
        {
            if (Children.Contains(c)) Console.WriteLine("Error: Type hierarchy contains cycle regarding tasks {0} and {1}.", this, c);
            else
            {
                if (!AncestorTypes.Contains(c))
                {
                    this.AncestorTypes.Add(c);
                    foreach (ConstantType cT in Children)
                    {
                        cT.AddAncestor(c);
                    }
                }
            }
        }
        /// <summary>
        /// Adds c to its children. Does not call its own ancestor as this is only my child. 
        /// But gives this child link to all my ancestors. 
        /// </summary>
        /// <param name="c"></param>
        public void AddChild(ConstantType c)
        {
            if (AncestorTypes.Contains(c)) Console.WriteLine("Error: Type hierarchy contains cycle regarding tasks {0} and {1}.", this, c);
            else
            {
                Children.Add(c);
                foreach (ConstantType ct in AncestorTypes)
                {
                    c.AddAncestor(ct);
                }
            }
        }


        /// <summary>
        /// Returns true if this type is a parent to the given type.
        /// </summary>
        /// <returns></returns>
        public bool IsAncestorTo(ConstantType givenType)
        {
            if (this.Name == "any") return true; //INFO any is child to everything. This is used for constants with unknown types. We dont allow methods that have unspecified type. As in we cannot have type all (unlless user defined) 
            if (givenType.AncestorTypes.Contains(this)) return true;
            return false;
        }
        /// <summary>
        /// Returns true if one of these types is a parent to the other. 
        /// </summary>
        /// <param name="givenType"></param>
        /// <returns></returns>
        public bool IsRelated(ConstantType givenType)
        {
            if (this.IsAncestorTo(givenType) || givenType.IsAncestorTo(this)) return true;
            return false;
        }

        public ConstantType(String Name)
        {
            this.Name = Name;
            this.AncestorTypes = new List<ConstantType>();
            this.AncestorTypes.Add(this);
            this.Instances = new List<Constant>();
            this.Children = new List<ConstantType>();
            this.DescendantTypes = new List<ConstantType>();
        }

        public override string ToString()
        {
            return this.Name;
        }

        /// <summary>
        /// Tells each of it's ancestors to add this as their descendant. 
        /// </summary>
        internal void CreateDescendantLine()
        {
            foreach (ConstantType c in AncestorTypes)
            {
                c.AddDescendant(this);
            }
        }

        private void AddDescendant(ConstantType c)
        {
            if (!DescendantTypes.Contains(c)) this.DescendantTypes.Add(c);
        }

        public override bool Equals(object obj)
        {
            return obj != null && obj is ConstantType constantType && this.Name == constantType.Name; 
        }

        public override int GetHashCode()
        {
            if (Name == null) return 0;
            return Name.GetHashCode();
        }
    }

}
