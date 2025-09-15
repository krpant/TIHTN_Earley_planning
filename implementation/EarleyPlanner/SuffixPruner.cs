using System.Collections.Generic;

namespace PlanRecognitionExtension
{
    using PlanRecognitionNETF;
    internal interface SuffixPruner
    {
        void ComputeSupports();
        List<List<Action>> GetPrunedPlanSuffix(List<Action> planPrefix, int suffixLength, List<ActionType> allActionTypes, List<Rule> allRules,
            List<TaskType> allTaskTypes, System.Threading.CancellationToken cancellationToken);
    }
}
