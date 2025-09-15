namespace PlanRecognitionNETF
{
    internal class ActionTaskType : TaskType
    {
        public ActionType ActionType { get; }
        public ActionTaskType(string name, int numOfVars, ActionType actionType) : base(name, numOfVars)
        {
            ActionType = actionType;
        }
    }
}
