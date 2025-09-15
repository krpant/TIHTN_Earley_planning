namespace PlanRecognitionExtension
{
    internal interface EarleyStateHeuristic
    {
        double ComputeHeuristic(EarleyParser.QueueItem queueItem, int iterationIndex);
    }
}
