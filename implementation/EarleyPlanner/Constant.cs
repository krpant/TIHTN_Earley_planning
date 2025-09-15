using System;

namespace PlanRecognitionNETF
{
    /// <summary>
    /// Represents a consatnt or a variable that can be put into parameters of tasks/actions.
    /// </summary>
    class Constant
    {
        public String Name { get;  } 
        public ConstantType Type { get; private set;  } 

        public Constant(string v, ConstantType constantType)
        {
            this.Name = v;
            this.Type = constantType;
        }

        public override string ToString()
        {
            String s = this.Name + " type: " + Type;
            return s;
        }

        public override bool Equals(object obj)
        {
            if (obj == null || GetType() != obj.GetType())
            {
                return false;
            }
            Constant cond2 = obj as Constant;
            if (Name.Equals(cond2.Name))
            {
                if (this.Type.IsRelated(cond2.Type)) return true;
                else return false;
            }
            else return false;
        }

        internal void SetType(ConstantType type) 
        {
            Type = type;
        }

        internal static bool ConstantEmpty(Constant constant)
        {
            return constant == null || constant.Name == null || constant.Name.Length == 0;
        }

        public override int GetHashCode() 
        {
            int hashCode = -243844509;
            if (Name != null)
            {
                hashCode = hashCode * -1521134295 + Name.GetHashCode();
            }
            hashCode = hashCode * -1521134295 + Type.GetHashCode();
            return hashCode;
        }
    }
}
