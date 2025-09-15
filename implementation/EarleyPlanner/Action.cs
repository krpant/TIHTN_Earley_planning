using System;

namespace PlanRecognitionExtension
{
    using PlanRecognitionNETF;
    internal class Action
    {
        public Action(ActionType actionType, Constant[] actionInstance)
        {
            ActionType = actionType;
            ActionInstance = actionInstance;
        }

        public void SetVariable(int index, Constant constant)
        {
            if (index < 0 || index >= ActionInstance.Length)
            {
                throw new ArgumentOutOfRangeException("Invalid index.");
            }
            ActionInstance[index] = constant;
        }

        // Creates uninstantiated action.
        public Action(ActionType actionType)
        {
            ActionType = actionType;
            ActionInstance = new Constant[actionType.ActionTerm.Variables.Length];
            for (int i = 0; i < actionType.ActionTerm.Variables.Length; i++)
            {
                ActionInstance[i] = new Constant(null, actionType.ActionTerm.Variables[i].Type);
            }
        }

        public ActionType ActionType { get; }
        public Constant[] ActionInstance { get; }

        public override bool Equals(object obj)
        {
            return obj != null && obj is Action action &&
                   ActionType.ActionTerm.Name == action.ActionType.ActionTerm.Name &&
                   ActionType.ActionTerm.Variables.Length == action.ActionType.ActionTerm.Variables.Length &&
                   ActionInstancesEqual(action.ActionInstance);
        }

        public static bool SameTypeActions(Action a1, Action a2)
        {
            return a1.ActionType.Equals(a2.ActionType);
        }

        private bool ActionInstancesEqual(Constant[] actionInstance)
        {
            if (actionInstance == null || ActionInstance.Length != actionInstance.Length)
            {
                return false;
            }
            for (int i = 0; i < ActionInstance.Length; i++)
            {
                if (ActionInstance[i] != null && actionInstance[i] != null)
                {
                    if (ActionInstance[i].Name != actionInstance[i].Name)
                    {
                        return false;
                    }
                    if (ActionInstance[i].Type != null && actionInstance[i].Type != null)
                    {
                        if (!ActionInstance[i].Type.IsRelated(actionInstance[i].Type))
                        {
                            return false;
                        }
                    }
                    else if (ActionInstance[i].Type != null || actionInstance[i].Type != null)
                    {
                        return false;
                    }
                }
                else if (ActionInstance[i] != null || actionInstance[i] != null)
                {
                    return false;
                }
            }
            return true;
        }

        public override int GetHashCode()
        {
            int hashCode = 653281691;
            hashCode = hashCode * -1521134295 + ActionType.ActionTerm.Name.GetHashCode();
            hashCode = hashCode * -1521134295 + ActionType.ActionTerm.Variables.Length;
            return hashCode;
        }

        public override string ToString()
        {
            string s = ActionType.ActionTerm.Name + "(";

            for (int i = 0; i < ActionInstance.Length; i++)
            {
                Constant c = ActionInstance[i];
                if (i > 0)
                {
                    s += ", ";
                }
                if (c != null && c.Name != null && c.Name.Length > 0)
                {
                    s += c.Name;
                }
                else
                {
                    s += "?";
                }
            }

            return s + ")";
        }

        internal bool Subsumes(Action subsumedAction)
        {
            if (subsumedAction == null || !ActionType.Equals(subsumedAction.ActionType))
            {
                return false;
            }
            for (int i = 0; i < ActionInstance.Length; i++)
            {
                if (Constant.ConstantEmpty(ActionInstance[i]))
                {
                    if (!Constant.ConstantEmpty(subsumedAction.ActionInstance[i]))
                    {
                        return false;
                    }
                }
                else if (!Constant.ConstantEmpty(subsumedAction.ActionInstance[i]))
                {
                    if (ActionInstance[i].Name != subsumedAction.ActionInstance[i].Name)
                    {
                        return false;
                    }
                }
            }
            return true;
        }

        internal Action Clone()
        {
            Constant[] constantsClone = new Constant[ActionInstance.Length];
            for (int i = 0; i < ActionInstance.Length;i++)
            {
                constantsClone[i] = new Constant(ActionInstance[i].Name, ActionInstance[i].Type);
            }
            return new Action(ActionType, constantsClone);
        }
    }
}
