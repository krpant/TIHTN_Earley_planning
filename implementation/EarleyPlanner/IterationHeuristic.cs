namespace PlanRecognitionExtension
{
    internal class IterationHeuristic : EarleyStateHeuristic
    {
        public double ComputeHeuristic(EarleyParser.QueueItem queueItem, int iterationIndex)
        {
            return iterationIndex;
        }
    }
}
