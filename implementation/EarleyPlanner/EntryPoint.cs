using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading;
using PlanRecognitionNETF;
using static PlanRecognitionExtension.EarleyParser;


namespace PlanRecognitionExtension
{
    internal class EntryPoint
    {
        enum ExitCode
        {
            Solved, OutOfTime, OutOfMemory, Exception
        }

        enum RecognizerType
        {
            Original, WithPruning, Earley, HeuristicEarley, POEarley, EarleyVerifier, GroundedEarleyVerifier, Planner,
            TIHTNPlannerInsertionOnTheFly, TIHTNPlannerInsertionAllAtOnce
        }

        static void Main(string[] args)
        {
#if (!DEBUG)
            try
#endif
            {
                // DEBUG START
                string benchmarksDir = @"..\TIHTN_Benchmarks";
                string domainS = @$"{benchmarksDir}\Pizza-TIHTN\domains\domain.hddl";
                string problemS = @$"{benchmarksDir}\Pizza-TIHTN\problems\pfile05.hddl";
                string planS = @"";
                string classicalPlanner = @"..\FD\fast-downward.py"; 

                string resultS = @"results.csv";
                string recognizerS = "ti2";
                int timeoutSeconds = 50000 * 60;


                bool POActionInsertionAllowed = true;
                bool POActionDeletionAllowed = false;
                bool POAnytimeGoals = true;
                bool returnFirstFoundSolution = false;

#if RELEASE
                POActionInsertionAllowed = true;
                POActionDeletionAllowed = true;
                POAnytimeGoals = true;
#endif

                if (args != null && args.Length >= 5 && (args[3] == "pl" || args[3] == "ti1" || args[3] == "ti2"))
                {
                    domainS = args[0];
                    problemS = args[1];
                    resultS = args[2];
                    recognizerS = args[3];
                    timeoutSeconds = int.Parse(args[4]);
                    POActionInsertionAllowed = true;
                    POActionDeletionAllowed = false;
                    POAnytimeGoals = false;

                    if (args.Length >= 6)
                    {
                        if (args[5].ToLower() == "y")
                        {
                            POAnytimeGoals = true;
                        }
                    }

                    if (args.Length >= 7)
                    {
                        if (args[6].ToLower() == "y")
                        {
                            returnFirstFoundSolution = true; 
                        }
                    }

                    if (args.Length >= 8)
                    {
                        classicalPlanner = args[7];
                    }
                }

                else if (args != null && args.Length >= 6)
                {
                    domainS = args[0];
                    problemS = args[1];
                    planS = args[2];
                    resultS = args[3];
                    recognizerS = args[4];
                    timeoutSeconds = int.Parse(args[5]);

                    if (recognizerS == "po")
                    {
                        if (args.Length >= 7)
                        {
                            if (args[6] == "n")
                            {
                                POActionInsertionAllowed = false;
                            }
                            if (args.Length >= 8)
                            {
                                if (args[7] == "n")
                                {
                                    POActionDeletionAllowed = false;
                                }

                                if (args.Length >= 9)
                                {
                                    if (args[8] == "n")
                                    {
                                        POAnytimeGoals = false;
                                    }
                                }
                            }

                        }
                    }

                }


#if (!DEBUG)
                if ((args.Length < 4) || (args.Length < 8 && (args[3] == "ti1" || args[3] == "ti2")))
                {
                    Console.WriteLine("Not enough arguments. Expects 8 arguments: domain file path, problem file path, output file path, result csv file path, " +
                        "\"ti1\" for TIHTN planner with insertion on the fly / \"ti2\" for optimal TIHTN planner" +
                        ", timeout in seconds " +
                        "'anytime goals' (y/n), 'return first solution' (y/n), Fast Downward path.");
                    return;
                }
                else if (args.Length < 6)
                {
                    Console.WriteLine("Not enough arguments. Expects 6 arguments: domain file path, problem file path, plan file path, result csv file path, \"o\" for the original recognizer, " +
                        "\"p\" for recognizer with pruning, \"e\" for Earley plan recognition, \"po\" for Earley recognition with partial observability, \"v\" for Earley verification, or \"g\" for Earley verification, timeout in seconds + in case of partial observability 'action insertion allowed' (y/n), 'action deletion allowed' (y/n) and " +
                        "'anytime goals' (y/n).");
                    return;
                }
#endif


                CancellationTokenSource cts = new CancellationTokenSource();
                cts.CancelAfter(TimeSpan.FromSeconds(timeoutSeconds));
                CancellationToken cancellationToken = cts.Token;
                Stopwatch watch = Stopwatch.StartNew(); // total time includes reading
                List<TaskType> allTaskTypes = null;
                List<ActionType> allActionTypes = null;
                List<Term> initialState = null;
                List<ConstantType> allConstantTypes = null;
                List<Constant> allConstants = null;
                List<Rule> emptyRules = null;
                List<Rule> rules = null;
                List<Term> predicates = null;
                List<Action> planPrefix = null;
                Exception readingException = null;
                List<Term> plan = null;
                List<Task> initHtnTasks = null;

                    try
                {
                    Read(planS, domainS, problemS, out plan, out allTaskTypes, out allActionTypes,
                        out initialState,
                        out allConstantTypes, out allConstants, out emptyRules,
                        out rules, out planPrefix, out initHtnTasks, out predicates, recognizerS);
                }
                catch (Exception e)
                {
                    readingException = e;
                }

                bool isValid = false;
                Rule finalRule;
                Subplan finalSubtask = null;
                RecognizerType recognizerType = default;
                List<int> addedActionsByIteration = null;
                ExitCode exitCode;
                long elapsedMs;
                Exception exception = null;

                int POAddedActions = 0;
                int PODeletedActions = 0;
                string POCorrectedPlan = string.Empty;
                string POFoundGoalsWithTime = string.Empty;

#if (!DEBUG)
                try
#endif
                {
#if DEBUG      
                    StreamWriter sw = new(@"log.txt")
                    {
                        AutoFlush = true
                    };
                    Console.SetOut(sw);
#endif

                    if (recognizerS.ToLower() == "o")
                    {
                        Console.WriteLine("Original recognizer started...");
                        recognizerType = RecognizerType.Original;
                        isValid = RunOriginalRecognizer(plan, allTaskTypes, allActionTypes, initialState, allConstantTypes, allConstants, emptyRules, out finalRule,
                            out finalSubtask, out addedActionsByIteration, cancellationToken);
                    }
                    else if (recognizerS.ToLower() == "p")
                    {
                        Console.WriteLine("Recognizer with Earley pruning started...");
                        recognizerType = RecognizerType.WithPruning;
                        isValid = RunRecognizerWithPruning(plan, allTaskTypes, allActionTypes, initialState, allConstantTypes, allConstants, emptyRules, rules, planPrefix,
                            out finalRule, out finalSubtask, out addedActionsByIteration, cancellationToken);
                    }
                    else if (recognizerS.ToLower() == "e")
                    {
                        Console.WriteLine("Earley recognizer started...");
                        recognizerType = RecognizerType.Earley;
                        isValid = RunEarleyRecognizer(plan, allTaskTypes, allActionTypes, initialState, allConstantTypes, allConstants, emptyRules, rules, planPrefix,
                            out finalRule, out finalSubtask, out addedActionsByIteration, cancellationToken);
                    }
                    else if (recognizerS.ToLower() == "v")
                    {
                        Console.WriteLine("Earley verifier started...");
                        recognizerType = RecognizerType.EarleyVerifier;
                        isValid = RunEarleyVerifier(plan, allTaskTypes, allActionTypes, initialState, allConstantTypes, allConstants, emptyRules, rules, planPrefix,
                            out finalRule, out finalSubtask, out addedActionsByIteration, cancellationToken);
                    }
                    else if (recognizerS.ToLower() == "g")
                    {
                        Console.WriteLine("Grounded Earley verifier started...");
                        recognizerType = RecognizerType.GroundedEarleyVerifier;
                        if (readingException == null)
                        {
                            isValid = RunGroundedEarleyVerifier(plan, allTaskTypes, allActionTypes, initialState, allConstantTypes, allConstants, emptyRules, rules, planPrefix,
                            out finalRule, out finalSubtask, out addedActionsByIteration, cancellationToken);
                        }
                        else
                        {
                            exitCode = ExitCode.Solved; 
                        }
                    }
                    else if (recognizerS.ToLower() == "h")
                    {
                        Console.WriteLine("Earley recognizer with heuristic started...");
                        recognizerType = RecognizerType.HeuristicEarley;
                        isValid = RunEarleyRecognizerWithHeuristic(plan, allTaskTypes, allActionTypes, initialState, allConstantTypes, allConstants, emptyRules, rules, planPrefix,
                            out finalRule, out finalSubtask, out addedActionsByIteration, cancellationToken);
                    }
                    else if (recognizerS.ToLower() == "po")
                    {
                        Console.WriteLine("Partially observable Earley recognizer with heuristic started...");
                        recognizerType = RecognizerType.POEarley;
                        isValid = RunPOEarley(plan, allTaskTypes, allActionTypes, initialState, allConstantTypes, allConstants, emptyRules, rules, planPrefix, 
                            POActionInsertionAllowed, POActionDeletionAllowed, POAnytimeGoals,
                            out finalRule, out finalSubtask, out addedActionsByIteration, cancellationToken, watch, out POAddedActions, out PODeletedActions, out POCorrectedPlan,
                            out POFoundGoalsWithTime);
                    }
                    else if (recognizerS.ToLower() == "pl")
                    {
                        Console.WriteLine("Earley planner started...");
                        recognizerType = RecognizerType.Planner;
                        isValid = RunPlanner(plan, allTaskTypes, allActionTypes, initialState, allConstantTypes, allConstants, emptyRules, 
                            rules, planPrefix,
                            POAnytimeGoals,
                            out finalRule, out finalSubtask, out addedActionsByIteration, cancellationToken, watch, out POAddedActions, 
                             out POCorrectedPlan,
                            out POFoundGoalsWithTime, initHtnTasks);
                    }
                    else if (recognizerS.ToLower() == "ti1")
                    {
                        Console.WriteLine("TIHTN planning started...");
                        recognizerType = RecognizerType.TIHTNPlannerInsertionOnTheFly;
                        isValid = RunTIHTNPlanner(classicalPlanner, allTaskTypes, allActionTypes, initialState, allConstantTypes, allConstants,
                            emptyRules, rules, predicates,
                            POAnytimeGoals, out finalRule, out finalSubtask, cancellationToken, watch, out POAddedActions,
                            out POCorrectedPlan,
                            out POFoundGoalsWithTime,
                            initHtnTasks, TIHTNPlanner.TaskInsertionMode.InsertOnTheFly, true);
                    }
                    else if (recognizerS.ToLower() == "ti2")
                    {
                        Console.WriteLine("TIHTN planning started...");
                        recognizerType = RecognizerType.TIHTNPlannerInsertionAllAtOnce;
                        isValid = RunTIHTNPlanner(classicalPlanner, allTaskTypes, allActionTypes, initialState, allConstantTypes, allConstants,
                            emptyRules, rules, predicates,
                            POAnytimeGoals, out finalRule, out finalSubtask, cancellationToken, watch, out POAddedActions,
                            out POCorrectedPlan,
                            out POFoundGoalsWithTime,
                            initHtnTasks, TIHTNPlanner.TaskInsertionMode.InsertAllAtOnce, returnFirstFoundSolution);
                    }
                    else
                    {
                        Console.WriteLine("Last argument is invalid - expected \"o\" for the original recognizer or \"p\" for recognizer with pruning.");
                        return;
                    }

                    if (cancellationToken.IsCancellationRequested)
                    {
                        exitCode = ExitCode.OutOfTime;
                    }
                    else
                    {
                        exitCode = ExitCode.Solved;
                    }
                }
#if (!DEBUG)
                catch (Exception ex)
                {
                    if (ex is OutOfMemoryException)
                    {
                        exitCode = ExitCode.OutOfMemory;
                    }

                    else
                    {
                        exitCode = ExitCode.Exception;
                        exception = ex;
                    }

                }
#endif

                watch.Stop();
                elapsedMs = watch.ElapsedMilliseconds;
                int prefixLength = plan != null ? plan.Count : 0;
                if (recognizerType != RecognizerType.POEarley && recognizerType != RecognizerType.EarleyVerifier
                    && recognizerType != RecognizerType.GroundedEarleyVerifier && recognizerType != RecognizerType.Planner
                    && recognizerType != RecognizerType.TIHTNPlannerInsertionOnTheFly 
                    && recognizerType != RecognizerType.TIHTNPlannerInsertionAllAtOnce)
                {
                    WriteStatsToCsvFile(planS, domainS, problemS, resultS, prefixLength, finalSubtask, recognizerType, exitCode, elapsedMs, 
                        addedActionsByIteration, exception);
                }
                else if (recognizerType == RecognizerType.POEarley || recognizerType == RecognizerType.Planner)
                {
                    WritePOCsvFile(recognizerType, planS, domainS, problemS, resultS, finalSubtask, exitCode, elapsedMs, POAddedActions, PODeletedActions, 
                        POCorrectedPlan, POFoundGoalsWithTime, POActionInsertionAllowed, POActionDeletionAllowed,
                        exception);
                }
                else if (recognizerType == RecognizerType.EarleyVerifier || recognizerType == RecognizerType.GroundedEarleyVerifier)
                {
                    WriteVerificationStatsToCsvFile(planS, domainS, problemS, resultS, prefixLength, finalSubtask, recognizerType, 
                        exitCode, elapsedMs, addedActionsByIteration, exception);
                }
                else if (recognizerType == RecognizerType.TIHTNPlannerInsertionOnTheFly 
                    || recognizerType == RecognizerType.TIHTNPlannerInsertionAllAtOnce)
                {
                    WriteTIHTNcsvFile(recognizerType, domainS, problemS, resultS, exitCode, elapsedMs, POCorrectedPlan, POFoundGoalsWithTime,
                        exception);
                }

                WriteConsoleOutput(planS, domainS, problemS, isValid, elapsedMs, finalSubtask, recognizerType, exitCode, exception);

                Console.WriteLine("Finished.");
#if DEBUG

#endif


            }

#if (!DEBUG)
            catch (Exception e)
            {
                Console.WriteLine(e.Message);
                Console.WriteLine(e.StackTrace);
            }
#endif
        }

        private static void WriteTIHTNcsvFile(RecognizerType recognizerType, string domainS, string problemS, string resultS, 
            ExitCode exitCode, long elapsedMs, string pOCorrectedPlan, string pOFoundGoalsWithTime, Exception exception)
        {
            bool writeHeader = !File.Exists(resultS);
            using (StreamWriter csvWriter = new StreamWriter(resultS, true))
            {
                StringBuilder stringBuilder = new StringBuilder();

                if (writeHeader)
                {
                    string s = "planner; problem name; solved?; time (ms); plan length; plan; found goals (goal, length, time); " +
                        "exception; domain file; problem file; ";
                    csvWriter.WriteLine(s);
                }
                AppendToCsv(stringBuilder, recognizerType.ToString());
                string problemName = Path.GetFileNameWithoutExtension(problemS);
                
                AppendToCsv(stringBuilder, problemName);
                AppendToCsv(stringBuilder, exitCode.ToString());

                if (exitCode == ExitCode.Solved)
                {
                    AppendToCsv(stringBuilder, elapsedMs.ToString());
                }
                else
                {
                    AppendToCsv(stringBuilder, "");
                }
                if (pOCorrectedPlan.Length > 0)
                {
                    AppendToCsv(stringBuilder, pOCorrectedPlan.Count(x => x == ')').ToString());
                }
                else
                {
                    AppendToCsv(stringBuilder, "");
                }
                AppendToCsv(stringBuilder, pOCorrectedPlan);
                AppendToCsv(stringBuilder, pOFoundGoalsWithTime);


                if (exitCode == ExitCode.Exception)
                {
                    AppendToCsv(stringBuilder, exception.ToString());
                }
                else
                {
                    AppendToCsv(stringBuilder, "");
                }

                AppendToCsv(stringBuilder, domainS);
                AppendToCsv(stringBuilder, problemS);

                csvWriter.WriteLine(stringBuilder.ToString());
            }
        }

        private static bool RunTIHTNPlanner(string classicalPlannerPath, List<TaskType> allTaskTypes, List<ActionType> allActionTypes, List<Term> initialState, 
            List<ConstantType> allConstantTypes, List<Constant> allConstants, List<Rule> emptyRules, List<Rule> rules,
            List<Term> allPredicates,
            bool pOAnytimeGoals, out Rule finalRule, out Subplan finalSubtask, CancellationToken cancellationToken, Stopwatch watch, 
            out int pOAddedActions, out string foundPlanString, out string pOFoundGoalsWithTime, List<Task> initHtnTasks, 
            TIHTNPlanner.TaskInsertionMode taskInsertionMode, bool returnFirstResult)
        {
            PlanRecognizerExtended.AddTaskToActionRules(allActionTypes, rules, allTaskTypes);
            TIHTNPlanner planner = new TIHTNPlanner(classicalPlannerPath, allTaskTypes, allActionTypes, allConstants, allConstantTypes, initialState,
                initHtnTasks, allPredicates, rules, true, false, pOAnytimeGoals, returnFirstResult, taskInsertionMode);


            List<Rule> allRulesWithEmptyRules = new(rules);
            allRulesWithEmptyRules.AddRange(emptyRules);

            bool result = planner.RunPOPlanRecognition(Enumerable.Empty<Term>().ToList(), Enumerable.Empty<Action>().ToList(), 
                initialState, 
                allRulesWithEmptyRules, out finalRule, out finalSubtask, out List<int> _,
                cancellationToken, new PartialObservabilityEarleyParser.MinFlawsIncludingUncoveredActionsHeuristic(0), 
                out List<ActionSubplan> foundPlan, watch, out pOFoundGoalsWithTime);
            if (foundPlan != null)
            {
                pOAddedActions = foundPlan.Count;
                foundPlanString = string.Join(", ", foundPlan);
            }
            else
            {
                pOAddedActions = 0;
                foundPlanString = "";
            }
            WritePlannerSolution(finalSubtask, foundPlan, planner, pOAnytimeGoals, 
                out int addedActions, out string planString);
            
            return result;
        }

        private static bool RunGroundedEarleyVerifier(List<Term> plan, List<TaskType> allTaskTypes, List<ActionType> allActionTypes, 
            List<Term> initialState, List<ConstantType> allConstantTypes, List<Constant> allConstants, List<Rule> emptyRules, List<Rule> rules, List<Action> planPrefix, out Rule finalRule, out Subplan finalSubtask, out List<int> addedActionsByIteration, CancellationToken cancellationToken)
        {
            PlanRecognizerExtended.AddTaskToActionRules(allActionTypes, rules, allTaskTypes);
            EarleyParser planR = new GroundedEarleyParser(allTaskTypes, allActionTypes, allConstants, allConstantTypes, initialState);
            return planR.VerifyPlanByEarleyParser(plan, planPrefix, initialState,
                        rules, out finalRule, out finalSubtask, out addedActionsByIteration, cancellationToken);
        }

        internal static void WritePlannerSolution(Subplan finalSubtask, List<ActionSubplan> foundPlan, PartialObservabilityEarleyParser parser,
            bool anytimeGoals,
            out int addedActions, 
            out string planString, string hSpace = "", bool writeHeader = true)
        {
            addedActions = 0;
            planString = "";

            if (writeHeader)
            {
                Console.WriteLine("*************************************************************************");
                Console.WriteLine($"ANYTIME PLANS: {anytimeGoals}");
            }
            if (finalSubtask != null)
            {
                if (writeHeader)
                {
                    Console.WriteLine("PLAN LENGTH: " + foundPlan.Count);
                    Console.WriteLine("PLAN:");
                }

                string line;
                for (int indexInSolution = 0; indexInSolution < foundPlan.Count; indexInSolution++)
                {
                    line = $"{foundPlan[indexInSolution]}";
                    Console.WriteLine(line);
                    AddLineToPlanString(ref planString, line);
                    addedActions++;
                }
            }
            else
            {
                Console.WriteLine("NO PLAN FOUND.");
            }
            if (writeHeader)
            {
                Console.WriteLine("*************************************************************************");
            }

        }

        internal static void WritePlannerSolution(List<ActionSubplan> bestPlanSoFar)
        {
            for (int i = 0; i < bestPlanSoFar.Count; i++)
            {
                Console.WriteLine($"{i}: {bestPlanSoFar[i]}");
            }
        }

        internal static void WritePOSolution(Subplan finalSubtask, List<ActionSubplan> foundPlan, PartialObservabilityEarleyParser parser, bool actionInsertionAllowed, bool actionDeletionAllowed, bool anytimeGoals,
            out int addedActions, out int deletedActions, 
            out string planString, string hSpace = "", bool writeHeader = true)
        {
            addedActions = 0;
            deletedActions = 0;
            planString = "";

            if (writeHeader)
            {
                Console.WriteLine("*************************************************************************");
                Console.WriteLine($"ACTION INSERTION ALLOWED: {actionInsertionAllowed}");
                Console.WriteLine($"ACTION DELETION ALLOWED: {actionDeletionAllowed}");
                Console.WriteLine($"ANYTIME GOALS: {anytimeGoals}");
            }
            if (finalSubtask != null)
            {
                if (writeHeader)
                {
                    Console.WriteLine("NUMBER OF FLAWS: " + parser.ComputeNumberOfFlaws(finalSubtask));
                    Console.WriteLine("CORRECTED PLAN:");
                }

                int indexInPlan = 0;
                string line;
                for (int indexInSolution = 0; indexInSolution < foundPlan.Count; indexInSolution++)
                {
                    EarleyParser.ActionSubplan a = foundPlan[indexInSolution];
                    if (a.IsInPlan)
                    {
                        while (!a.Subplan.Equals(parser.PlanPrefix[indexInPlan]))
                        {
                            line = $"{hSpace} - {indexInPlan}: {parser.PlanPrefix[indexInPlan].ActionString(0)}";
                            AddLineToPlanString(ref planString, line);
                            Console.WriteLine(line);
                            deletedActions++;
                            indexInPlan++;
                        }

                        line = $"{hSpace}{indexInPlan}: {finalSubtask.ActionString(indexInSolution)}";
                        AddLineToPlanString(ref planString, line);
                        Console.WriteLine(line);

                        indexInPlan++;
                    }
                    else
                    {
                        line = $"{hSpace} + {finalSubtask.ActionString(indexInSolution)}";
                        Console.WriteLine(line);
                        AddLineToPlanString(ref planString, line);
                        addedActions++;
                    }
                }
                while (indexInPlan < parser.PlanPrefix.Count)
                {
                    line = $"{hSpace} - {indexInPlan}: {parser.PlanPrefix[indexInPlan].ActionString(0)}";
                    AddLineToPlanString(ref planString, line);
                    Console.WriteLine(line);
                    deletedActions++;
                    indexInPlan++;
                }
            }
            else
            {
                Console.WriteLine("NO PLAN FOUND.");
            }
            if (writeHeader)
            {
                Console.WriteLine("*************************************************************************");
            }
        }

        private static void AddLineToPlanString(ref string planString, string line)
        {
            if (planString.Length > 0)
            {
                planString += ", ";
            }
            planString += line;
        }



        private static void WriteConsoleOutput(string planS, string domainS, string problemS, bool isValid, long elapsedMs, 
            Subplan finalSubtask, RecognizerType recognizerType, ExitCode exitCode, Exception exception = null)
        {
            Console.WriteLine("Domain: " + domainS);
            Console.WriteLine("Problem: " + problemS);
            Console.WriteLine("Plan: " + planS);
            switch (recognizerType)
            {
                case RecognizerType.WithPruning: Console.WriteLine("Plan recognition with pruning (Earley CFG parser):");
                    break;
                case RecognizerType.Original: Console.WriteLine("Plan recognition without pruning:");
                    break;
                case RecognizerType.EarleyVerifier: Console.WriteLine("Earley plan verification:");
                    break;
                case RecognizerType.Planner: Console.WriteLine("Earley planner:");
                    break;
                case RecognizerType.TIHTNPlannerInsertionAllAtOnce: Console.WriteLine("TITHN planner - insertion all at once:");
                    break;
                case RecognizerType.TIHTNPlannerInsertionOnTheFly: Console.WriteLine("TIHTN planner - insertion on the fly");
                    break;


            }
            switch (exitCode)
            {
                case ExitCode.Solved:
                    if (isValid)
                    {
                        Console.WriteLine("Plan is valid.");
                        Console.WriteLine("Total time: " + elapsedMs / 1000f + " s");
                        Console.WriteLine("Root task: " + new Task(finalSubtask.TaskType, finalSubtask.TaskInstance.Variables));
                        if (recognizerType != RecognizerType.TIHTNPlannerInsertionOnTheFly
                            && recognizerType != RecognizerType.TIHTNPlannerInsertionAllAtOnce)
                        {
                            finalSubtask.WritePlan();
                        }
                        finalSubtask.WriteHistory();
                    }
                    else
                    {
                        Console.WriteLine("Plan is invalid.");
                        Console.WriteLine("Total time: " + elapsedMs / 1000f + " s");
                    }
                    break;
                case ExitCode.OutOfTime:
                    Console.WriteLine("Out of time.");
                    break;
                case ExitCode.OutOfMemory:
                    Console.WriteLine("Out of memory.");
                    break;
                case ExitCode.Exception:
                    Console.WriteLine(exception.Message);
                    Console.WriteLine(exception.StackTrace);
                    break;
            }

        }

        static void WritePOCsvFile(RecognizerType recognizerType, string planS, string domainS, string problemS, string resultS,
            Subplan finalSubtask, ExitCode exitCode, long time, int addedActions, int deletedActions, string planString, 
            string foundGoalsWithTime, bool actionInsertionAllowed, bool actionDeletionAllowed, Exception exception = null)
        {
            bool writeHeader = !File.Exists(resultS);
            using (StreamWriter csvWriter = new StreamWriter(resultS, true))
            {
                StringBuilder stringBuilder = new StringBuilder();

                if (writeHeader)
                {
                    string s = "plan name; action insertion?; action deletion?; solved?; time (ms); plan length; total flaws; added actions; deleted actions; plan; found goals (goal, flaws, time); " +
                        "exception; domain file; problem file; plan file; ";
                    csvWriter.WriteLine(s);
                }

                if (recognizerType != RecognizerType.Planner)
                {
                    string planSConverted = planS.Replace('/', '\\');
                    int i1 = planSConverted.LastIndexOf('\\');
                    int i2 = planSConverted.LastIndexOf('.');
                    AppendToCsv(stringBuilder, planS.Substring(i1 + 1, i2 - i1 - 1));
                }
                else
                {
                    AppendToCsv(stringBuilder, "");
                }

                AppendToCsv(stringBuilder, actionInsertionAllowed ? "Yes" : "No");
                AppendToCsv(stringBuilder, actionDeletionAllowed ? "Yes" : "No");


                AppendToCsv(stringBuilder, exitCode.ToString());

                if (exitCode == ExitCode.Solved) 
                {
                    AppendToCsv(stringBuilder, time.ToString());
                }
                else
                {
                    AppendToCsv(stringBuilder, "");
                }

                if (finalSubtask != null)
                {
                    AppendToCsv(stringBuilder, finalSubtask.PlanLength().ToString());
                    AppendToCsv(stringBuilder, (addedActions + deletedActions).ToString());
                    AppendToCsv(stringBuilder, addedActions.ToString());
                    AppendToCsv(stringBuilder, deletedActions.ToString());
                    AppendToCsv(stringBuilder, planString);
                    AppendToCsv(stringBuilder, foundGoalsWithTime);
                }
                else
                {
                    for (int i = 0; i < 6; i++)
                    {
                        AppendToCsv(stringBuilder, "");
                    }
                }

                if (exitCode == ExitCode.Exception)
                {
                    AppendToCsv(stringBuilder, exception.ToString());
                }
                else
                {
                    AppendToCsv(stringBuilder, "");
                }
                AppendToCsv(stringBuilder, domainS);
                AppendToCsv(stringBuilder, problemS);
                AppendToCsv(stringBuilder, planS);

                csvWriter.WriteLine(stringBuilder.ToString());
            }
        }

        private static void WriteVerificationStatsToCsvFile(string planS, string domainS, string problemS, string resultS,
            int planLength, Subplan finalSubtask, RecognizerType recognizerType, ExitCode exitCode, long time, List<int> addedActions, Exception exception = null)
        {
            bool writeHeader = !File.Exists(resultS);
            using (StreamWriter csvWriter = new StreamWriter(resultS, true))
            {
                StringBuilder stringBuilder = new StringBuilder();

                if (writeHeader)
                {
                    // plan prefix name; recognizer; solved (yes/OutOfTime/OutOfMemory/exception thrown);  time (ms); prefix length;  plan length;     plan (comma-separated actions);
                    // total added actions;     added actions in each iteration (comma-separated); exception (if solved=E)     
                    // domain path;     problem path;   plan prefix path; 
                    string s = "plan name; verifier; solved?; valid?; time (ms); plan length; " +
                        "exception; domain file; problem file; prefix file; ";
                    csvWriter.WriteLine(s);
                }

                string planSConverted = planS.Replace('/', '\\');
                int i1 = planSConverted.LastIndexOf('\\');
                int i2 = planSConverted.LastIndexOf('.');
                AppendToCsv(stringBuilder, planS.Substring(i1 + 1, i2 - i1 - 1));
                AppendToCsv(stringBuilder, recognizerType.ToString());
                AppendToCsv(stringBuilder, exitCode.ToString());

                AppendToCsv(stringBuilder, (finalSubtask != null).ToString());

                if (exitCode == ExitCode.Solved)
                {
                    AppendToCsv(stringBuilder, time.ToString());
                }
                else
                {
                    AppendToCsv(stringBuilder, "");
                }

                AppendToCsv(stringBuilder, planLength.ToString());

                if (exitCode == ExitCode.Exception)
                {
                    AppendToCsv(stringBuilder, exception.ToString());
                }
                else
                {
                    AppendToCsv(stringBuilder, "");
                }
                AppendToCsv(stringBuilder, domainS);
                AppendToCsv(stringBuilder, problemS);
                AppendToCsv(stringBuilder, planS);

                csvWriter.WriteLine(stringBuilder.ToString());
            }
        }

        private static void WriteStatsToCsvFile(string planS, string domainS, string problemS, string resultS,
            int prefixLength, Subplan finalSubtask, RecognizerType recognizerType, ExitCode exitCode, long time, List<int> addedActions, Exception exception = null)
        {
            bool writeHeader = !File.Exists(resultS);
            using (StreamWriter csvWriter = new StreamWriter(resultS, true))
            {
                StringBuilder stringBuilder = new StringBuilder();

                if (writeHeader) 
                {
                    // plan prefix name; recognizer; solved (yes/OutOfTime/OutOfMemory/exception thrown);  time (ms); prefix length;  plan length;     plan (comma-separated actions);
                    // total added actions;     added actions in each iteration (comma-separated); exception (if solved=E)     
                    // domain path;     problem path;   plan prefix path; 
                    string s = "prefix name; recognizer; solved?; time (ms); prefix length; plan length; plan; " +
                        "total added actions; added actions by iterations; exception; domain file; problem file; prefix file; ";
                    csvWriter.WriteLine(s);
                }

                if (planS.Length > 0)
                {
                    string planSConverted = planS.Replace('/', '\\');
                    int i1 = planSConverted.LastIndexOf('\\');
                    int i2 = planSConverted.LastIndexOf('.');
                    AppendToCsv(stringBuilder, planS.Substring(i1 + 1, i2 - i1 - 1));
                }
                else
                {
                        AppendToCsv(stringBuilder, "");
                }


                AppendToCsv(stringBuilder, recognizerType.ToString());
                AppendToCsv(stringBuilder, exitCode.ToString());

                if (exitCode == ExitCode.Solved)
                {
                    AppendToCsv(stringBuilder, time.ToString());
                    AppendToCsv(stringBuilder, prefixLength.ToString());
                    AppendToCsv(stringBuilder, finalSubtask.PlanLength().ToString());
                    AppendToCsv(stringBuilder, finalSubtask.GetPlanString());
                    AppendToCsv(stringBuilder, addedActions.Sum().ToString());

                    StringBuilder addedActionsS = new StringBuilder();
                    for (int i = 0; i < addedActions.Count; i++)
                    {
                        if (i > 0)
                        {
                            addedActionsS.Append(", ");
                        }
                        addedActionsS.Append(addedActions[i].ToString());
                    }

                    AppendToCsv(stringBuilder, addedActionsS.ToString());
                }
                else
                {
                    AppendToCsv(stringBuilder, "");
                    AppendToCsv(stringBuilder, prefixLength.ToString());
                    for (int i = 0; i < 4; i++)
                    {
                        AppendToCsv(stringBuilder, "");
                    }
                }
                if (exitCode == ExitCode.Exception)
                {
                    AppendToCsv(stringBuilder, exception.ToString());
                }
                else
                {
                    AppendToCsv(stringBuilder, "");
                }
                AppendToCsv(stringBuilder, domainS);
                AppendToCsv(stringBuilder, problemS);
                AppendToCsv(stringBuilder, planS);

                csvWriter.WriteLine(stringBuilder.ToString());
            }
        }

        static void AppendToCsv(StringBuilder stringBuilder, string s)
        {
            stringBuilder.Append(s);
            stringBuilder.Append("; ");
        }

        private static bool RunEarleyRecognizer(List<Term> plan,
            List<TaskType> allTaskTypes, List<ActionType> allActionTypes, List<Term> initialState, List<ConstantType> allConstantTypes, List<Constant> allConstants,
            List<Rule> emptyRules, List<Rule> rules, List<Action> planPrefix, out Rule finalRule, out Subplan finalSubtask, out List<int> addedActionsByIteration,
            CancellationToken cancellationToken)
        {
            PlanRecognizerExtended.AddTaskToActionRules(allActionTypes, rules, allTaskTypes);
            List<Rule> allRulesWithEmptyRules = new List<Rule>(rules);
            allRulesWithEmptyRules.AddRange(emptyRules);
            EarleyParser planR = new EarleyParser(allTaskTypes, allActionTypes, allConstants, allConstantTypes, initialState);
            return planR.RecognizePlanByEarleyParser(plan, planPrefix, initialState,
                        allRulesWithEmptyRules, out finalRule, out finalSubtask, out addedActionsByIteration, cancellationToken);
        }

        private static bool RunEarleyVerifier(List<Term> plan,
            List<TaskType> allTaskTypes, List<ActionType> allActionTypes, List<Term> initialState, List<ConstantType> allConstantTypes, List<Constant> allConstants,
            List<Rule> emptyRules, List<Rule> rules, List<Action> planPrefix, out Rule finalRule, out Subplan finalSubtask, out List<int> addedActionsByIteration,
            CancellationToken cancellationToken)
        {
            PlanRecognizerExtended.AddTaskToActionRules(allActionTypes, rules, allTaskTypes);
            EarleyParser planR = new EarleyParser(allTaskTypes, allActionTypes, allConstants, allConstantTypes, initialState);
            List<Rule> allRulesWithEmptyRules = new List<Rule>(rules);
            allRulesWithEmptyRules.AddRange(emptyRules);
            return planR.VerifyPlanByEarleyParser(plan, planPrefix, initialState,
                       allRulesWithEmptyRules, out finalRule, out finalSubtask, out addedActionsByIteration, cancellationToken);
        }

        private static bool RunPlanner(List<Term> plan, List<TaskType> allTaskTypes, List<ActionType> allActionTypes, List<Term> initialState, List<ConstantType> allConstantTypes, List<Constant> allConstants,
            List<Rule> emptyRules, List<Rule> rules, List<Action> planPrefix, 
            bool anytimeGoals, out Rule finalRule, out Subplan finalSubtask, out List<int> addedActionsByIteration,
            CancellationToken cancellationToken, Stopwatch watch, out int addedActions, out string planString, 
            out string foundGoalsWithTime, List<Task> toGoals)
            {
            PlanRecognizerExtended.AddTaskToActionRules(allActionTypes, rules, allTaskTypes);
            PartialObservabilityEarleyParser planR = new EarleyPlanner(allTaskTypes, allActionTypes, allConstants, allConstantTypes,
                initialState, toGoals, anytimeGoals);
            List<Rule> allRulesWithEmptyRules = new(rules);
            allRulesWithEmptyRules.AddRange(emptyRules);
            bool result = planR.RunPOPlanRecognition(plan, planPrefix, initialState, allRulesWithEmptyRules, out finalRule, out finalSubtask, out addedActionsByIteration,
                cancellationToken, new PartialObservabilityEarleyParser.MinFlawsIncludingUncoveredActionsHeuristic(plan.Count), out List<ActionSubplan> foundPlan, watch, out foundGoalsWithTime);
            WritePlannerSolution(finalSubtask, foundPlan, planR, anytimeGoals, out addedActions, out planString);
            return result;
        }

        private static bool RunPOEarley(List<Term> plan, List<TaskType> allTaskTypes, List<ActionType> allActionTypes, List<Term> initialState, List<ConstantType> allConstantTypes, List<Constant> allConstants,
            List<Rule> emptyRules, List<Rule> rules, List<Action> planPrefix, bool actionInsertionAllowed, bool actionDeletionAllowed,
            bool anytimeGoals, out Rule finalRule, out Subplan finalSubtask, out List<int> addedActionsByIteration,
            CancellationToken cancellationToken, Stopwatch watch, out int addedActions, out int deletedActions, out string planString, out string foundGoalsWithTime)
        {
            PlanRecognizerExtended.AddTaskToActionRules(allActionTypes, rules, allTaskTypes);
            PartialObservabilityEarleyParser planR = new PartialObservabilityEarleyParser(allTaskTypes, allActionTypes, allConstants, allConstantTypes,
                initialState, actionInsertionAllowed, actionDeletionAllowed, anytimeGoals);
            List<Rule> allRulesWithEmptyRules = new List<Rule>(rules);
            allRulesWithEmptyRules.AddRange(emptyRules);
            bool result = planR.RunPOPlanRecognition(plan, planPrefix, initialState, allRulesWithEmptyRules, out finalRule, out finalSubtask, out addedActionsByIteration,
                cancellationToken, new PartialObservabilityEarleyParser.MinFlawsIncludingUncoveredActionsHeuristic(plan.Count), out List<ActionSubplan> foundPlan, watch, out foundGoalsWithTime);
            WritePOSolution(finalSubtask, foundPlan, planR, actionInsertionAllowed, actionDeletionAllowed, anytimeGoals, out addedActions, out deletedActions, out planString);
            return result;
        }

        private static bool RunEarleyRecognizerWithHeuristic(List<Term> plan,
            List<TaskType> allTaskTypes, List<ActionType> allActionTypes, List<Term> initialState, List<ConstantType> allConstantTypes, List<Constant> allConstants,
            List<Rule> emptyRules, List<Rule> rules, List<Action> planPrefix, out Rule finalRule, out Subplan finalSubtask, out List<int> addedActionsByIteration,
            CancellationToken cancellationToken)
        {
            PlanRecognizerExtended.AddTaskToActionRules(allActionTypes, rules, allTaskTypes);
            EarleyParser planR = new EarleyParser(allTaskTypes, allActionTypes, allConstants, allConstantTypes, initialState);

            EarleyStateHeuristic heuristic = new IterationHeuristic();

            return planR.RecognizePlanByEarleyParser(plan, planPrefix, initialState,
                        rules, out finalRule, out finalSubtask, out addedActionsByIteration, cancellationToken, heuristic);
        }

        private static bool RunRecognizerWithPruning(List<Term> plan,
            List<TaskType> allTaskTypes, List<ActionType> allActionTypes, List<Term> initialState, List<ConstantType> allConstantTypes, List<Constant> allConstants,
            List<Rule> emptyRules, List<Rule> rules, List<Action> planPrefix, out Rule finalRule, out Subplan finalSubtask, out List<int> addedActionsByIteration,
            CancellationToken cancellationToken)
        {
            PlanRecognizerExtended.AddTaskToActionRules(allActionTypes, rules, allTaskTypes);
            PlanRecognizerExtended planR = new PlanRecognizerExtended();
            return planR.RecognizePlanWithEarleyPruning(plan, planPrefix, allTaskTypes, allActionTypes, initialState, allConstants,
                        allConstantTypes, emptyRules, rules, out finalRule, out finalSubtask, out addedActionsByIteration, cancellationToken);
        }

        private static bool RunOriginalRecognizer(List<Term> plan,
            List<TaskType> allTaskTypes, List<ActionType> allActionTypes, List<Term> initialState, List<ConstantType> allConstantTypes, List<Constant> allConstants,
            List<Rule> emptyRules, out Rule finalRule, out Subplan finalSubtask, out List<int> addedActionsByIteration, CancellationToken cancellationToken)
        {
            PlanRecognisor planR = new PlanRecognisor();
            return planR.RecognizePlan(plan, allTaskTypes, allActionTypes, initialState, allConstants, allConstantTypes, emptyRules,
                 out finalRule, out finalSubtask, out addedActionsByIteration, cancellationToken);
        }

        private static void Read(string planS, string domainS, string problemS, out List<Term> plan, out List<TaskType> allTaskTypes,
            out List<ActionType> allActionTypes, out List<Term> initialState, out List<ConstantType> allConstantTypes, out List<Constant> allConstants,
            out List<Rule> emptyRules, out List<Rule> rules, out List<Action> planPrefix, out List<Task> initHtnTasks, out List<Term> predicates,
            string recogType)
        {
            InputReader reader = new InputReader();
            reader.ReadDomain(domainS);
            allActionTypes = reader.globalActions;
            allConstantTypes = reader.allConstantTypes;
            initialState = reader.ReadProblem(problemS, allConstantTypes, ref reader.allConstants);
            emptyRules = reader.emptyRules;
            allConstants = reader.allConstants;
            predicates = reader.allPredicates;
            if (recogType != "pl" && !recogType.StartsWith("ti"))
            {
                reader.ReadPlan(planS, allActionTypes, allConstants, out planPrefix);
                plan = reader.myActions;
            }
            else
            {
                plan = new();
                planPrefix = new();
            }
            allTaskTypes = reader.alltaskTypes;
            rules = reader.allRules;
            initHtnTasks = reader.initialHtnTasks;
        }
    }
}
