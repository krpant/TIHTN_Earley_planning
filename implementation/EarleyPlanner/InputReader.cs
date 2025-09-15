using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using PlanRecognitionExtension;

namespace PlanRecognitionNETF
{
    /// <summary>
    /// Takes the input and creates all neccessary structures. 
    /// </summary>
    class InputReader
    {
        /// <summary>
        /// Represnets the stae we are currently in
        /// </summary>
        enum State { inMethod, inSubtasks, nowhere, inTaskInfo, ordering, conditions, inAction, actPrecond, actEffects, inTypes, inConstants, betweenConditions, inPredicates };
        /// <summary>
        /// There are three types of ordering and each of them must be treated differently. 
        /// </summary>
        enum Ordering { Preset, Later, None };
        public List<ActionType> globalActions;
        public List<TaskType> alltaskTypes;
        public List<Rule> allRules;
        public List<Rule> emptyRules = new List<Rule>();
        public List<Term> myActions = new List<Term>();
        public List<ConstantType> allConstantTypes = new List<ConstantType>();
        public List<Constant> allConstants = new List<Constant>();
        public List<Task> initialHtnTasks = new(); // for planning
        bool forall = false;
        Constant forallConst = null; //so far we just allow one.
        string curRuleName = ""; 
        public List<Term> allPredicates = new();

        /// <summary>
        /// Reads the main and creates all rules and actions.
        /// </summary>
        /// <param name="fileName"></param>
        public void ReadDomain(String fileName)
        {
            System.IO.StreamReader file = new System.IO.StreamReader(fileName);
            String line;
            Ordering ordering = Ordering.None;
            State state = State.inTaskInfo;
            alltaskTypes = new List<TaskType>();
            Rule curRule = new Rule();
            allRules = new List<Rule>();
            List<Constant> paramTypeInfo = new List<Constant>();
            List<String> parameters = new List<string>();
            List<Tuple<TaskType, String, int>> namedTasks = new List<Tuple<TaskType, string, int>>();
            List<TaskType> curSubtaskList = new List<TaskType>();
            List<List<int>> referenceLists = new List<List<int>>();
            Rule lastRule = null;
            ActionType curActionType = new ActionType();
            int num = 0;
            List<Tuple<Term, bool>> preconditions = new List<Tuple<Term, bool>>();
            List<Tuple<List<int>, Term, bool>> betweenConditions = new List<Tuple<List<int>, Term, bool>>();
            globalActions = new List<ActionType>();
            int subtaskCount = 0;
            //Determines whether we are done in this specific section
            bool doneSubtask = false;
            bool doneConditions = false;
            bool doneConstants = false;
            bool doneActEff = false;
            bool doneOrder = false;
            String actName = "";
            bool lastInConditions = false;
            while ((line = file.ReadLine()) != null)
            {
                if (!line.Trim().StartsWith(";;") && line.Trim().Length > 0) 
                {
                    line = line.ToLower(); 
                    line = line.Trim(); 
                    line = line.Replace('\t', ' '); 
                    line = Regex.Replace(line, @"_+", "_"); // added because of inconsistent number of trailing _ in grounder output
                    if (line.Contains(":predicates"))
                    {
                        state = State.inPredicates;
                    }
                    if (line.Contains(":types"))
                    {
                        state = State.inTypes;
                    }
                    if (line.Contains(":constants"))
                    {
                        state = State.inConstants;
                    }
                    if (state == State.inPredicates && !line.Contains(":predicates"))
                    {
                        if (line.Trim().Equals(")"))
                        {
                            state = State.inTaskInfo;
                        }
                        else
                        {
                            ProcessPredicate(line, allConstantTypes);
                        }
                    }
                    if (state == State.inTypes)
                    {
                        if (line.Trim().Equals(")"))
                        {
                            FinishTypeHierarchy(ref allConstantTypes);
                            state = State.inTaskInfo;
                        }
                        else
                        {
                            CreateTypeHieararchy(line, allConstantTypes);
                        }
                    }
                    if (state == State.inConstants)
                    {
                        if (line.Trim().Equals(")"))
                        {
                            state = State.inTaskInfo;
                        }
                        else
                        {
                            GetConstants(line, ref allConstants, allConstantTypes);
                            doneConstants = CheckParenthesis(line) > 0;
                            if (doneConstants)
                            {
                                state = State.inTaskInfo;
                                doneConstants = false;
                            }
                        }

                    }
                    if (state == State.inTaskInfo && line.Contains(":task"))
                    {
                        //Getting list of all tasks
                        TaskType tT = CreateTaskType(line);
                        alltaskTypes.Add(tT);
                    }
                    if (line.Contains("(:method")) 

                    {
                        state = State.inMethod;
                        namedTasks = new List<Tuple<TaskType, string, int>>();
                        num = 0;
                        string[] items = line.Split(new char[] { ' ' }, StringSplitOptions.RemoveEmptyEntries);
                        curRuleName = items[1];
                    }
                    if (line.Contains("(:action"))
                        state = State.inAction;
                    if (state == State.inMethod)
                    {
                        if (line.Trim().Equals(")") && lastInConditions)
                        {
                            //This is an empty rule.                        
                            CreateConditions(curRule, preconditions);
                            preconditions = new List<Tuple<Term, bool>>();
                            emptyRules.Add(curRule);
                            lastInConditions = false;
                            curRule.Name = curRuleName;
                            curRule = new Rule();
                        }
                        if (line.Contains(":parameters"))
                        {
                            paramTypeInfo = GetParameters(line, allConstantTypes);
                            if (paramTypeInfo != null)
                            {
                                parameters = paramTypeInfo.Select(x => x.Name).ToList();
                                curRule.AllVars = parameters; //This will change later but at least for conditions we must have it already.
                                curRule.AllVarsTypes = paramTypeInfo.Select(x => x.Type).ToList();
                            }
                            else
                            {

                            }
                        }
                        else if (line.Contains(":task"))
                        {
                            //Getting  main task
                            List<int> refList;
                            TaskType tT = CreateTaskType(line, alltaskTypes, ref paramTypeInfo, out refList, allConstants);
                            TaskType t = FindTask(tT, alltaskTypes);
                            curRule.MainTaskType = t;
                            curRule.MainTaskReferences = refList;
                        }
                        else if (line.Contains(":subtasks") || line.Contains(":ordered-subtasks") || line.Contains(":ordered-tasks")) // added 3rd option
                        {
                            lastInConditions = false;
                            state = State.inSubtasks;
                            subtaskCount = 0;
                            if (line.Contains("ordered")) ordering = Ordering.Preset;
                            doneSubtask = false;
                        }
                        else if (line.Contains(":ordering"))
                        {
                            state = State.ordering;
                            num = 0;
                        }
                        else if (line.Contains(":precondition"))
                        {
                            state = State.conditions;
                            doneConditions = false;

                        }
                        else if (line.Contains(":between-condition"))
                        {
                            state = State.betweenConditions;
                        }
                    }
                    else if (state == State.conditions)
                    {
                        //Checks if there are more closed parenthesis and this section is over. 
                        if (forall) doneConditions = CheckParenthesis(line) > 1; // one closed parenthesis is from forall. 
                        else doneConditions = CheckParenthesis(line) > 0;
                        if (line.Trim().Equals(")"))
                        {
                            state = State.inMethod;
                        }
                        else
                        {
                            Tuple<Term, bool> condition = CreateCondition(line, ref paramTypeInfo, allConstants);
                            if (condition != null) preconditions.Add(condition);
                            if (doneConditions)
                            {
                                //If the rule is empty as in has no subtasks than this is the last thing it will go through.
                                state = State.inMethod;
                                lastInConditions = true;
                            }
                        }

                    }
                    else if (state == State.betweenConditions)
                    {
                        doneConditions = CheckParenthesis(line) > 0;
                        if (line.Trim().Equals(")"))
                        {
                            state = State.inMethod;
                        }
                        else
                        {
                            line = line.Replace("(", "");
                            string[] parts = line.Split(); //line loks like this:     1 2 powerco-of ?town ?powerco))
                            while (parts.Length >= 1 && parts[0] == "")
                            {
                                parts = (string[])parts.Skip(1).ToArray();
                            }
                            try
                            {
                                List<int> betweenTasks = new List<int>();
                                betweenTasks.Add(Int32.Parse(parts[0]));
                                betweenTasks.Add(Int32.Parse(parts[1]));
                                line = line.Replace(Int32.Parse(parts[0]) + " " + Int32.Parse(parts[1]) + " ", ""); //Now this looks like a normal condition.     powerco-of ?town ?powerco))
                                Tuple<Term, bool> condition = CreateCondition(line, ref paramTypeInfo, allConstants);
                                betweenConditions.Add(new Tuple<List<int>, Term, bool>(betweenTasks, condition.Item1, condition.Item2));
                                if (doneConditions)
                                {
                                    //If the rule is empty as in has no substasks than this is the last thing it will go through. But this cannot happen with between conditions anyway.
                                    state = State.inMethod;
                                    lastInConditions = true;
                                }
                            }
                            catch (Exception e)
                            {
                                Console.WriteLine("Error: Invalid description of a between condition: " + line);
                            }
                        }

                    }

                    else if (state == State.inSubtasks)
                    {
                        if (!line.Trim().Equals(")"))
                        {
                            //Checks if there are more closed parenthesis and this section is over. 
                            doneSubtask = CheckParenthesis(line) > 0;
                            if (subtaskCount == 0 && ordering != Ordering.Preset)
                            {
                                //Only check this if ordering is not preset. Cause then I know the ordering. 
                                int parenthesisCount = line.Count(x => x == '(');
                                if (parenthesisCount > 1) ordering = Ordering.Later;
                                else ordering = Ordering.None;

                            }
                            if (ordering == Ordering.Preset || ordering == Ordering.None)
                            {
                                //Ordered subtask looks almost the same as regular tasks. 
                                List<int> refList = new List<int>();

                                TaskType tT = CreateTaskType(line, alltaskTypes, ref paramTypeInfo, out refList, allConstants);
                                TaskType t = FindTask(tT, alltaskTypes);
                                if (t == tT)
                                {
                                    alltaskTypes.Add(t);
                                }
                                if (!t.Rules.Contains(curRule)) t.AddRule(curRule); //what if one rule has same tasktype twice? //We will put it in the rule multiple times. BUt the rule should only be once in the task. 
                                referenceLists.Add(refList);
                                curSubtaskList.Add(t);
                                subtaskCount++;
                            }
                            else
                            {
                                //Unordered subtask. After subtasks there will be ordering.
                                List<int> refList = new List<int>();
                                Tuple<TaskType, string> tupleTaskName = CreateNamedTaskType(line, 
                                    alltaskTypes, ref paramTypeInfo, out refList, allConstants);
                                Tuple<TaskType, string, int> tupleFull = new Tuple<TaskType, string, int>(tupleTaskName.Item1, tupleTaskName.Item2, num);
                                namedTasks.Add(tupleFull);
                                TaskType t = FindTask(tupleTaskName.Item1, alltaskTypes);  //Finds the task in lists of all tasks. 
                                if (t == tupleTaskName.Item1)
                                {
                                    alltaskTypes.Add(t);
                                }
                                if (!t.Rules.Contains(curRule)) t.AddRule(curRule); //Adds a link from this tasktype to the rule. 
                                curSubtaskList.Add(t);
                                referenceLists.Add(refList);
                                num++;
                                subtaskCount++;
                            }

                        }
                        if (line.Trim().Equals(")") || doneSubtask == true)
                        {
                            //WE have all the infromation about the rule we need now it's time to properly create it. 
                            CreateConditions(curRule, preconditions);
                            CreateBetweenConditions(curRule, betweenConditions);
                            if (paramTypeInfo != null)
                            {
                                curRule.AllVars = paramTypeInfo.Select(x => x.Name).ToList();
                                curRule.AllVarsTypes = paramTypeInfo.Select(x => x.Type).ToList();
                            }
                            curRule.TaskTypeArray = curSubtaskList.ToArray();
                            curRule.Finish(referenceLists);
                            if (ordering == Ordering.Preset) curRule.CreateOrder();
                            curSubtaskList = new List<TaskType>();
                            referenceLists = new List<List<int>>();

                            if (curRule.TaskTypeArray != null && curRule.TaskTypeArray.Length > 0)
                            {
                                allRules.Add(curRule);
                            }
                            else
                            {
                                emptyRules.Add(curRule);
                            }

                            lastRule = curRule; //for ordering
                            curRule.Name = curRuleName;
                            curRule = new Rule();
                            if (ordering != Ordering.Later) state = State.nowhere;
                            else state = State.inMethod;
                            parameters = new List<string>();
                            preconditions = new List<Tuple<Term, bool>>();
                            betweenConditions = new List<Tuple<List<int>, Term, bool>>();
                            ordering = Ordering.None;
                            subtaskCount = 0;
                        }
                    }
                    else if (state == State.ordering)
                    {
                        doneOrder = CheckParenthesis(line) > 0;
                        if (!line.Trim().Equals(")"))
                        {
                            CreateOrder(line, namedTasks, ref lastRule);
                        }
                        if (line.Trim().Equals(")") || doneOrder)
                        {
                            num = 0;
                            namedTasks = new List<Tuple<TaskType, string, int>>();
                            state = State.nowhere;
                            ordering = Ordering.None;
                        }


                    }
                    else if (state == State.inAction)
                    {
                        List<Constant> actVars = new List<Constant>();
                        if (line.Contains(":action"))
                        {
                            if (curActionType.ActionTerm != null) // for actions without preconditions or effects
                            {
                                if (curActionType.ActionTerm.Name != null)
                                    globalActions.Add(curActionType);
                                curActionType = new ActionType();
                            }
                            actName = GetActionName(line);
                        }
                        else if (line.Contains("parameters"))
                        {
                            actVars = GetParameters(line, allConstantTypes);
                            if (actVars == null)
                            {
                                actVars = new List<Constant>(0); 
                            }
                            curActionType.ActionTerm = new Term(actName, actVars.ToArray());
                        }
                        else if (line.Contains(":precondition"))
                        {
                            state = State.actPrecond;
                        }
                    }
                    if (state == State.actPrecond) //since preconditions have the first condition on the same line as the declaration this must be if and not else if. 
                    {
                        bool isPos;
                        if (line.Contains(":effect"))
                        {
                            state = State.actEffects;
                        }
                        else
                        {
                            if (!(line.Contains(":precondition"))) 
                            {
                                Tuple<String, List<int>> condition = GetActionCondition(line, curActionType.ActionTerm.Variables.Select(x => x.Name).ToList(), out isPos);
                                if (condition != null)
                                {
                                    if (isPos) curActionType.PosPreConditions.Add(condition);
                                    else curActionType.NegPreConditions.Add(condition);
                                }
                            }
                        }

                    }
                    if (state == State.actEffects)
                    {
                        if (forall) doneActEff = CheckParenthesis(line) > 1;
                        else doneActEff = CheckParenthesis(line) > 0;
                        if (!line.Trim().Equals(")"))
                        {
                            bool isPos;
                            if (!line.Trim().Equals(""))
                            {
                                Tuple<String, List<int>> condition = GetActionCondition(line, curActionType.ActionTerm.Variables.Select(x => x.Name).ToList(), out isPos);
                                if (condition != null)
                                {
                                    if (isPos) curActionType.PosPostConditions.Add(condition);
                                    else curActionType.NegPostConditions.Add(condition);
                                }
                            }
                        }
                        if (line.Trim().Equals(")") || doneActEff)
                        {
                            if (curActionType.ActionTerm != null)
                            {
                                if (curActionType.ActionTerm.Name != null) globalActions.Add(curActionType);
                                curActionType = new ActionType();
                            }
                        }
                    }
                }
            }
            if (curActionType.ActionTerm != null) // for action without preconditions and effects
            {
                if (curActionType.ActionTerm.Name != null) globalActions.Add(curActionType);
            }
        }

        private void ProcessPredicate(string line, List<ConstantType> allConstantTypes)
        {
            line = line.Replace("(", "").Replace(")", "");
            string[] items = line.Split(' ', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries);
            string termName = items[0];
            List<Constant> termParams = new List<Constant>();
            for (int i = 1; i < items.Length; i += 3)
            {
                string argName = items[i];
                string argType = items[i + 2];

                ConstantType constantType = FindConstantType(argType, allConstantTypes);
                Constant constant = new(argName, constantType);
                termParams.Add(constant);
            }

            Term predicate = new(termName, termParams.ToArray());
            allPredicates.Add(predicate);
        }

        ConstantType FindConstantType(string constTypeName, List<ConstantType> allConstantTypes)
        {
            return allConstantTypes.Where(x => x.Name == constTypeName).First();
        }

        /// <summary>
        /// Reads constant from list of constants.Line looks like this:fema ebs police-chief - callable
        /// </summary>
        /// <param name="line"></param>
        /// <param name="allConstants"></param>
        /// <param name="allConstantTypes"></param>     
        private void GetConstants(string line, ref List<Constant> allConstants, List<ConstantType> allConstantTypes)
        {
            line = line.Replace("(", "");
            line = line.Replace(")", "");
            int index = line.IndexOf(";;"); //Removes everything after ;; which symbolizes comment
            if (index > 0)
            {
                line = line.Substring(0, index);
            }
            string[] parts = line.Trim().Split();
            if (parts.Length < 1) return;
            while (parts.Length >= 1 && parts[0] == "")
            {
                parts = (string[])parts.Skip(1).ToArray();
            }
            if (parts.Length < 1) return;
            String s = parts[parts.Length - 1]; //The final type. In example it's callable.
            ConstantType t = ContainsType(allConstantTypes, s);
            if (t == null)
            {
                //This type does not exist. 
                if (parts[0] == ":constants") return;
                Console.WriteLine("Error:Constants have non existent Type {0}", s);
                return;
            }
            parts[parts.Length - 1] = null;
            foreach (String m in parts)
            {
                if (m != null && m != "-")
                {
                    Constant c1 = new Constant(m, t);
                    allConstants.Add(c1);
                }
            }
        }

        /// <summary>
        /// I have created the entire type hierarchy. Now I must add type any which is a child to everything.  
        /// This is used in rules or actiontypes, when we have a constant without a type. 
        /// Can also be used to ignore all types.        ///
        /// </summary>
        /// <param name="types"></param>
        private void FinishTypeHierarchy(ref List<ConstantType> types)
        {
            ConstantType any = new ConstantType("any");
            foreach (ConstantType c in types)
            {
                any.AddAncestor(c);
                c.AddChild(any);
                c.CreateDescendantLine();
            }
            any.CreateDescendantLine();
            types.Add(any);
        }

        //line looks like this:
        //waterco powerco - callable
        private void CreateTypeHieararchy(string line, List<ConstantType> types)
        {
            string[] parts = line.Trim().Split(); 
            if (line.Trim().Equals("(:types")) return;
            String s = parts[parts.Length - 1]; //The final type.
            ConstantType t = ContainsType(types, s);
            if (t == null)
            {
                //This type does not exist create it. 
                t = new ConstantType(s);
                types.Add(t);
            }
            parts[parts.Length - 1] = null;
            foreach (String m in parts)
            {
                if (m != null && m != "-")
                {
                    ConstantType t1 = ContainsType(types, m);
                    if (t1 == null)
                    {
                        t1 = new ConstantType(m);
                        types.Add(t1);
                    }
                    t1.AddAncestor(t);
                    t.AddChild(t1);

                }
            }

        }

        private ConstantType ContainsType(List<ConstantType> types, String name)
        {
            foreach (ConstantType type in types)
            {
                if (type.Name.Equals(name)) return type;
            }
            return null;
        }

        private string GetActionName(string line)
        {
            line = line.Replace("(:action ", "");
            line = line.Trim();
            return line;
        }

        private int CheckParenthesis(string line)
        {
            int openParenthesisCount = line.Count(x => x == '(');
            int closedParenthesisCount = line.Count(x => x == ')');
            return closedParenthesisCount - openParenthesisCount;
        }


        private Tuple<string, List<int>> GetActionCondition(string line, List<string> vars, out bool isPos)
        {
            if (forall == true) forall = false;
            bool isPositive = true;
            Tuple<string, List<int>> myCondition;
            line = line.Replace(":precondition ", "");
            line = line.Replace(" (and", "");
            line = line.Replace(":effect", "");
            bool skip = false;
            if (line.Contains("(not"))
            {
                line = line.Replace("(not", "");
                isPositive = false;
            }
            isPos = isPositive;
            line = line.Replace(")", "");
            line = line.Replace("(", "");
            string[] parts = line.Split(); 
            if (parts.Length < 1) return null;
            while (parts.Length >= 1 && parts[0] == "")
            {
                parts = (string[])parts.Skip(1).ToArray();
            }
            if (parts.Length < 1) return null;
            string name = parts[0];
            if (name.Trim().Equals("exists")) return null;//Currently ignores both exists conditions, which is proper behaviour. 
            if (name.Trim().Equals("forall"))
            {
                for (int i = 1; i + 2 < parts.Length; i = i + 3)
                {
                    name = parts[i];
                    ConstantType t = allConstantTypes.Where(x => x.Name.Equals(parts[i + 2])).FirstOrDefault();
                    if (t == null) t = allConstantTypes.Where(x => x.Name.Equals("any")).FirstOrDefault();
                    forallConst = new Constant(name, t);
                    vars.Add("!" + name);
                }
                return null;
            }
            string[] myVars = (string[])parts.Skip(1).ToArray();
            List<int> references = new List<int>();
            foreach (string var in myVars)
            {
                if (!var.Equals("-"))
                {
                    int i = vars.IndexOf(var);
                    if (i == -1) i = vars.IndexOf("!" + var); //In case this links to forall constant. 
                    if (i == -1)
                    {
                        if (!var.StartsWith("?"))
                        {
                            //this is a constant
                            vars.Add(var); //To remember what constant we shall add it to name of this condition 
                            //As action is just a term.  
                            name = name + "!" + var;
                            i = -3;

                        }
                        else
                        {
                            vars.Add(var);
                            i = -2; //this is either exists or forall condition.
                        }
                    }
                    references.Add(i);
                }
            }
            forallConst = null;
            myCondition = new Tuple<string, List<int>>(name, references);
            return myCondition;
        }

        TaskType FindTask(string name, List<TaskType> alltaskTypes)
        {
            foreach (TaskType taskType in alltaskTypes)
            {
                if (taskType.Name == name)
                {
                    return taskType;
                }
            }

            throw new ArgumentException($"Task type {name} is not defined.");
        }

        Task CreateTask(string name, string[] parameters, List<TaskType> allTaskTypes, List<Constant> allConstants)
        {
            TaskType tt = FindTask(name, alltaskTypes);

            if (tt.NumOfVariables != parameters.Length)
            {
                throw new ArgumentException($"Invalid parameters for task {name}: {string.Join(", ", parameters)}");
            }

            List<Constant> taskConstants = new();

            for (int i = 0; i < parameters.Length; i++)
            {
                string param = parameters[i];
                Constant constant = new(null, tt.TaskTerm.Variables[i].Type);

                if (!param.StartsWith('?'))
                {
                    constant = FindConstant(param, allConstants) ?? throw new ArgumentException($"Constant {name} is not defined.");
                    if (!constant.Type.Equals(tt.TaskTerm.Variables[i].Type) && !tt.TaskTerm.Variables[i].Type.IsAncestorTo(constant.Type))
                    
                    {
                        throw new ArgumentException($"Invalid parameter {param} for task {name}.");
                    }
                    
                }

                taskConstants.Add(constant);
            }

            return new Task(tt, taskConstants.ToArray());
        }

        private TaskType FindTask(TaskType tT, List<TaskType> alltaskTypes)
        {
            foreach (TaskType t in alltaskTypes)
            {
                if (t.Name == tT.Name && t.NumOfVariables == tT.NumOfVariables) return t;
            }
            return tT;
        }

        //Creates proper rule conditions.
        private void CreateConditions(Rule curRule, List<Tuple<Term, bool>> preconditions)
        {
            List<string> methodParams = curRule.AllVars;
            List<int> varReferences = new List<int>();
            Tuple<int, String, List<int>> condition;
            if (curRule.posPreConditions == null) curRule.posPreConditions = new List<Tuple<int, string, List<int>>>();
            if (curRule.negPreConditions == null) curRule.negPreConditions = new List<Tuple<int, string, List<int>>>();
            foreach (Tuple<Term, bool> cond in preconditions)
            {
                for (int i = 0; i < cond.Item1.Variables.Length; i++)
                {
                    int j = 0;
                    bool found = false;
                    foreach (String s in methodParams)
                    {
                        if (s.Equals(cond.Item1.Variables[i].Name) && curRule.AllVarsTypes[j] == cond.Item1.Variables[i].Type)
                        {
                            found = true;
                            break;
                        }
                        j++;
                    }
                    if (!found)
                    {
                        methodParams.Add(cond.Item1.Variables[i].Name);
                        curRule.AllVarsTypes.Add(cond.Item1.Variables[i].Type);
                    }
                    varReferences.Add(j);
                    if (j == -1 || j > methodParams.Count - 1)
                    {
                        if (cond.Item1.Variables[i] != forallConst && cond.Item1.Variables[i].Name.StartsWith("?"))
                            Console.WriteLine("Warning: Couldnt find condition {0} in allvars {1} in rule {2}. The program will still attempt to find the solution but it might have unexpected results. ", cond.Item1.Variables[i], string.Join(",", methodParams.ToArray()), curRule.MainTaskType.Name);
                        //If it doesnt start with a ? then it is a constant so of course its not in the main rule. It will be added later on. Non need to call warning
                    }
                }
                condition = new Tuple<int, string, List<int>>(0, cond.Item1.Name, varReferences);
                varReferences = new List<int>();

                if (cond.Item2) curRule.posPreConditions.Add(condition);
                else curRule.negPreConditions.Add(condition);



            }
        }

        /// <summary>
        /// Creates between conditions. 
        /// </summary>
        /// <param name="curRule"></param>
        /// <param name="betweenconditions"></param>
        private void CreateBetweenConditions(Rule curRule, List<Tuple<List<int>, Term, bool>> betweenconditions)
        {
            List<string> methodParams = curRule.AllVars;
            List<int> varReferences = new List<int>();
            Tuple<int, int, String, List<int>> condition;
            if (curRule.posBetweenConditions == null) curRule.posBetweenConditions = new List<Tuple<int, int, string, List<int>>>();
            if (curRule.negBetweenConditions == null) curRule.negBetweenConditions = new List<Tuple<int, int, string, List<int>>>();
            foreach (Tuple<List<int>, Term, bool> cond in betweenconditions)
            {
                for (int i = 0; i < cond.Item2.Variables.Length; i++)
                {
                    int j = 0;
                    foreach (String s in methodParams)
                    {
                        if (s.Equals(cond.Item2.Variables[i].Name) && curRule.AllVarsTypes[j] == cond.Item2.Variables[i].Type) break;
                        j++;
                    }
                    varReferences.Add(j);
                    if (j == -1 || j > methodParams.Count - 1)
                    {
                        if (cond.Item2.Variables[i] != forallConst && cond.Item2.Variables[i].Name.StartsWith("?")) Console.WriteLine("Warning: Coudnt find condition {0} in allvars {1} in rule {2}", cond.Item2.Variables[i], string.Join(",", methodParams.ToArray()), curRule.MainTaskType.Name);
                        //If it doesnt start with a ? then it is a constant so of course its not in the main rule. It will be added later on. Non need to call warning
                    }
                }
                condition = new Tuple<int, int, string, List<int>>(cond.Item1[0], cond.Item1[1], cond.Item2.Name, varReferences);
                varReferences = new List<int>();
                if (cond.Item3) curRule.posBetweenConditions.Add(condition);
                else curRule.negBetweenConditions.Add(condition);
            }
        }

        // line looks like this: (contentOf ?b ?c)
        // or like this: (not(= ?b ?b2))        
        //returns condition and bool is true if condition is positive false, if negative. 
        private Tuple<Term, bool> CreateCondition(string line, ref List<Constant> methodInfo, 
            List<Constant> allConstants)
        {

            if (forall == true) forall = false; //Last condition was for all now is the one it applies to. //TODo one forall is not allowed for mutliple conditions. 
            bool isPositive = true;
            if (line.Contains("(not(") || line.Contains("(not "))
            {
                line = line.Replace("(not", "");
                isPositive = false;
            }
            //now line loks like this> (contentOf ?b ?c) or this: (= ?b ?b2))
            line = line.Replace(")", ""); //(contentOf ?b ?c or this: (= ? b ? b2
            line = line.Replace("(", "").TrimEnd();
            int index = line.IndexOf(";;"); //Removes everything after ;; which symboliyes comment
            if (index > 0)
            {
                line = line.Substring(0, index);
            }
            string[] parts = line.Split(); 
            if (parts.Length < 1) return null;
            while (parts.Length >= 1 && parts[0] == "")
            {
                parts = (string[])parts.Skip(1).ToArray();
            }
            if (parts.Length < 1) return null;
            string name = parts[0];
            if (name.Trim().Equals("exists")) return null;
            if (name.Trim().Equals("forall"))
            {
                for (int i = 1; i + 2 < parts.Length; i = i + 3)
                {
                    name = parts[i];
                    ConstantType t = allConstantTypes.Where(x => x.Name.Equals(parts[i + 2])).FirstOrDefault();
                    if (t == null) t = allConstantTypes.Where(x => x.Name.Equals("any")).FirstOrDefault();
                    forallConst = new Constant("!" + name, t);
                    methodInfo.Add(forallConst);
                }
                return null;
            }
            string[] vars = (string[])parts.Skip(1).ToArray();
            List<Constant> conVars = new List<Constant>();
            foreach (String s in vars)
            {
                Constant c = FindConstant(s, methodInfo);
                ConstantType any = allConstantTypes.Where(x => x.Name.Equals("any")).FirstOrDefault();
                if (c == null)
                {
                    c = FindConstant("!" + s, methodInfo);
                    if (c == null)
                    {
                        //This constant is not in the rules paramaters. We should add it there. 
                        c = FindConstant(s, allConstants);
                        if (c == null) c = new Constant(s, any);
                        if (methodInfo == null)
                        {
                            methodInfo = new();
                        }
                        methodInfo.Add(c);
                    }

                }
                conVars.Add(c);
            }
            Term term = new Term(name, conVars.ToArray());
            Tuple<Term, bool> tuple = new Tuple<Term, bool>(term, isPositive);
            return tuple;
        }

        /// <summary>
        /// Creates method parameters (including the ?)
        /// The line loks like this: :parameters (?b1 ?b2 - bowl ?c1 ?c2 - content)      
        /// </summary>
        /// <param name="line"></param>
        /// <returns></returns>
        private List<Constant> GetParameters(string line, List<ConstantType> types)
        {
            List<Constant> parameters = new List<Constant>();
            line = line.Replace(":parameters ", ""); //The line loks like this:(?b1 ?b2 - bowl ?c1 <c2 - content)
            line = line.Replace("(", "");
            line = line.Replace(")", "");
            int index = line.IndexOf(";;"); //Removes everything after ;; which symboliyes comment
            if (index > 0)
            {
                line = line.Substring(0, index);
            }
            string[] parts = line.Trim().Split(new char[] {' ', '\t'}, StringSplitOptions.RemoveEmptyEntries); 
            List<String> curNames = new List<string>();
            ConstantType type;
            if (parts.Length < 1) return null;
            while (parts.Length >= 1 && parts[0].Trim() == "")
            {
                parts = (string[])parts.Skip(1).ToArray();
            }
            if (parts.Length < 1) return null;
            foreach (string par in parts)
            {
                if (par.Contains("?"))
                {
                    curNames.Add(par);
                }
                else
                {
                    if (par != "-" && par != ":parameters" )
                    {
                        type = types.Where(x => x.Name.Equals(par)).First();
                        if (curNames != null && curNames.Any())
                        {
                            foreach (String name in curNames)
                            {
                                parameters.Add(new Constant(name, type));
                            }
                        }
                        curNames = new List<string>();
                    }
                }

            }
            return parameters;
        }

        //The line loks like this: (st1 <st2)
        //The tuple is ordered the same way the tasks are in rule. So based on which tuple it is in list it is the num. 
        private void CreateOrder(string line, List<Tuple<TaskType, string, int>> namedTasks, ref Rule curRule)
        {
            if (line.Equals(")")) return;
            line = line.Replace("(", "");
            line = line.Replace(")", "");
            int index = line.IndexOf(";;"); //Removes everythign after ;; which symboliyes comment
            if (index > 0)
            {
                line = line.Substring(0, index);
            }
            string[] parts = line.Split(); 
            if (parts.Length == 0) return;
            while (parts.Length > 0 && parts[0] == "")
            {
                parts = (string[])parts.Skip(1).ToArray();
            }

            if (parts[0] != "<") Console.WriteLine("Error:Wrong ordering {0}", parts[0]);
            Tuple<TaskType, string, int> tuple1 = (Tuple<TaskType, string, int>)namedTasks.Where(c => c.Item2.Equals(parts[1])).First();
            Tuple<TaskType, string, int> tuple2 = (Tuple<TaskType, string, int>)namedTasks.Where(c => c.Item2.Equals(parts[2])).First();
            
            
            curRule.AddOrderCondition(tuple1.Item3, tuple2.Item3);
        }

        //The line loks like this: st1 (add cream ?b1))
        private Tuple<TaskType, String> CreateNamedTaskType(string line, List<TaskType> allTasks, 
            ref List<Constant> methodParam, out List<int> refList, List<Constant> fixedConstants)
        {
            string[] parts = line.Trim().Split('(');
            int index = line.IndexOf(";;"); //Removes everything after ;; which symboliyes comment
            if (index > 0)
            {
                line = line.Substring(0, index);
            }
            while (parts.Length > 0 && parts[0] == "")
            {
                parts = (string[])parts.Skip(1).ToArray();
            }
            string name = parts[0].Trim();
            if (parts.Length > 1) line = line.Replace(name, ""); //This means that there is ordering. Sometimes there is no ordering so if there is none then the task is just normal.              
            TaskType t = CreateTaskType(line, allTasks, ref methodParam, out refList, fixedConstants);
            return new Tuple<TaskType, string>(t, name);

        }

        ////The line loks like this: :task (makeNoodles ?n ?p)
        ///or like this:  (add water ?p)
        ///Depends on whether this is the main task of a rule or a subtask. 
        private TaskType CreateTaskType(string line, List<TaskType> allTasks, ref List<Constant> methodParam, out List<int> refList, List<Constant> fixedConstants)
        {
            refList = new List<int>();
            line = line.Replace(":task ", ""); //line:(makeNoodles ?n ?p)
            line = line.Replace("(", ""); //line makeNoodles ?n ?p or add water ?p
            line = line.Replace(")", "");
            int index = line.IndexOf(";;"); //Removes everything after ;; which symbolizes comment
            if (index > 0)
            {
                line = line.Substring(0, index);
            }
            string[] parts = line.Trim().Split(new char[] {' ', '\t'}, StringSplitOptions.RemoveEmptyEntries); 
            while (parts.Length > 0 && parts[0] == "")
            {
                parts = (string[])parts.Skip(1).ToArray();
            }
            string name = parts[0];
            string[] parameters = (string[])parts.Skip(1).ToArray();
            if (methodParam == null)
            {
                methodParam = new();
            }
            if (methodParam != null)
            {
                List<String> methodParNames = methodParam.Select(x => x.Name).ToList();
                foreach (string param in parameters)
                {
                    if (param != "")
                    {
                        if (!param.Contains("?"))
                        {
                            //It's not in method list we must add it.                     
                            if (!methodParNames.Contains(param))
                            {
                                Constant c = FindConstant(param, fixedConstants);
                                if (c == null)
                                {
                                    ConstantType a = allConstantTypes.Where(x => x.Name.Equals("any")).FirstOrDefault();
                                    c = new Constant(param, a);
                                    fixedConstants.Add(c);
                                }
                                methodParam.Add(c);
                                refList.Add(methodParam.Count - 1);
                            }
                            else
                            {
                                refList.Add(methodParNames.IndexOf(param));
                            }
                        }
                        else
                        {
                            refList.Add(methodParNames.IndexOf(param));
                        }
                    }
                }
            }
            TaskType tT = new TaskType(name, parameters.Length);
            return tT;
        }

        /// <summary>
        /// Gets a list of constants and a name and returns the constant associated to it. 
        /// </summary>
        /// <param name="param"></param>
        /// <param name="fixedConstants"></param>
        /// <returns></returns>
        internal static Constant FindConstant(string param, List<Constant> fixedConstants)
        {
            Constant c = fixedConstants?.Where(x => x.Name.Equals(param)).FirstOrDefault();
            return c;
        }

        //The line loks like this: (:task makeTomatoSoup :parameters (?p - cookingPot))
        private TaskType CreateTaskType(string line) //From list of main tasks
        {
            line = line.Replace("(:task ", ""); //line:makeTomatoSoup :parameters (?p - cookingPot))
            string[] parts = line.Trim().Split(); //parts: makeTomatoSoup :parameters (?p - cookingPot)) //TODO changed
            int index = line.IndexOf(";;"); //Removes everything after ;; which symbolizes comment
            if (index > 0)
            {
                line = line.Substring(0, index);
            }
            while (parts[0] == "")
            {
                parts = (string[])parts.Skip(1).ToArray();
            }
            String name = parts[0]; //makeTomatoSoup
            String[] parameters = (string[])parts.Skip(2).ToArray();// (? p - cookingPot))
            List<string> myParams = new List<string>();
            foreach (String possibleParam in parameters)
            {
                //TaskType does not care about the types in it. That is handled in rule production. It doesn't even cares what variables it has just the number. 
                if (possibleParam.Contains("?")) myParams.Add(possibleParam);               
            }
            TaskType tT = new TaskType(name, myParams.Count);

            int paramsStartIndex = line.IndexOf(":parameters");
            string paramsString= line.Substring(paramsStartIndex);
            List<Constant> taskTypeConstants = GetParameters(paramsString, allConstantTypes);
            if (taskTypeConstants == null)
            {
                taskTypeConstants = new List<Constant>(0);     
            }
            tT.TaskTerm = new Term(tT.Name, taskTypeConstants.ToArray());

            return tT;
        }

        /// <summary>
        /// Reads plan and returns it as terms. 
        /// </summary>
        /// <param name="fileName"></param>
        public List<Term> ReadPlan(String fileName, List<ActionType> allActionTypes, List<Constant> allConstants, 
            out List<PlanRecognitionExtension.Action> plan)
        { 
            System.IO.StreamReader file = new System.IO.StreamReader(fileName);
            myActions = new List<Term>();
            String line;
            plan = new List<PlanRecognitionExtension.Action>();
            while ((line = file.ReadLine()) != null)
            {
                line = line.ToLower(); 
                line = line.Trim(); 
                line = line.Replace('\t', ' ');
                line = Regex.Replace(line, @"_+", "_"); // added because of inconsistent number of trailing _ in grounder output

                string[] actions = line.Split('(');

                foreach (String a in actions)
                {
                    Term actionInstance = CreateActionInstance(a, allActionTypes, allConstants);
                    if (actionInstance != null)
                    {
                        ActionType aT = FindActionType(allActionTypes, actionInstance.Name, actionInstance.Variables.Count());
                        aT.Instances.Add(actionInstance);
                        myActions.Add(actionInstance);
                        plan.Add(new PlanRecognitionExtension.Action(aT, actionInstance.Variables));
                    }
                }
            }
            return myActions;

        }

        internal static ActionType FindActionType(List<ActionType> allActionTypes, string name, int vars)
        {
            return allActionTypes.Where(x => x.ActionTerm.Name.Equals(name) && x.ActionTerm.Variables.Count() == vars).FirstOrDefault();

        }

        /// <summary>
        /// Reads the file explaining the problem. 
        /// </summary>
        /// <param name="fileName"></param>
        public List<Term> ReadProblem(String fileName, List<ConstantType> allConstantTypes, ref List<Constant> constants)
        {
            List<Constant> inputConstants = new List<Constant>();
            System.IO.StreamReader file = new System.IO.StreamReader(fileName);
            String line;
            List<Term> conditions = new List<Term>();
            bool inInit = false;
            bool inObjects = false;

            bool inHtn = false;
            bool inHtnSubtasks = false;
            bool moreHtnSubtasks = false;
            bool inHtnOrdering = false;
            bool moreHtnOrderings = false;

            Dictionary<string, Task> initHtnTasksByIDs = new();
            Dictionary<string, List<string>> orderingConstraints = new Dictionary<string, List<string>>();

            while ((line = file.ReadLine()) != null)
            {
                if (!line.Trim().StartsWith(";;") && line.Trim().Length > 0)      { 
                    line = line.ToLower(); 
                    line = line.Trim(); 
                    line = line.Replace('\t', ' '); 
                    line = Regex.Replace(line, @"_+", "_"); // added because of inconsistent number of trailing _ in grounder output
                                                            

                    if (line.Trim().Equals(")") && inInit == true) return conditions;
                    if (line.Contains(":init")) inInit = true;
                    if (line.Contains(":objects")) inObjects = true;

                    else if (line.Contains(":htn"))
                    {
                        inHtn = true;
                        inObjects = false;
                    }

                    else if (inInit == true)
                    {
                        string[] parts = Regex.Split(line, @"(?=\()");
                        foreach (string part in parts)
                        {
                            Term c = CreateStateCondition(part, ref inputConstants, constants);
                            if (c != null) conditions.Add(c);
                        }
                    }
                    else if (inObjects == true)
                    {
                        if (line.Trim().Equals(")"))
                        {
                            inObjects = false;
                            AddNewConstants(inputConstants, ref constants); //Adds inputconstants in constants. Check uniqueness and substitute constantswith type any if possible.                         
                        }
                        GetConstants(line, ref inputConstants, allConstantTypes);
                    }
                    else if (inHtnOrdering)
                    {
                        if (line.Trim() == ")")
                        {
                            if (moreHtnOrderings)
                            {
                                moreHtnOrderings = false;
                            }
                            else
                            {
                                inHtnOrdering = false;

                                SortHtnTasks(initHtnTasksByIDs, orderingConstraints);
                            }
                        }

                        else
                        {
                            string l = line.Trim();
                            if (!l.StartsWith('(') || !l.EndsWith(')'))
                            {
                                throw new FormatException($"Invalid ordering format: {l}");
                            }

                            l = l.Replace("(", "").Replace(")", "");

                            string[] items = l.Split(' ', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries);

                            if (items.Length != 3 || items[0] != "<")
                            {
                                throw new FormatException($"Invalid ordering format: {l}");
                            }

                            string task1 = items[1];
                            string task2 = items[2];

                            if (!initHtnTasksByIDs.ContainsKey(task1) || !initHtnTasksByIDs.ContainsKey(task2))
                            {
                                throw new FormatException($"Invalid ordering format: {l}");
                            }

                            if (!orderingConstraints.TryGetValue(task1, out _))
                            {
                                orderingConstraints[task1] = new();
                            }
                            orderingConstraints[task1].Add(task2);
                        }
                    }
                    else if (inHtnSubtasks)
                    {
                        if (line.Contains(":ordering"))
                        {
                            inHtnOrdering = true;
                            inHtnSubtasks = false;

                            if (line.Trim() == "(and")
                            {
                                moreHtnOrderings = true;
                            }
                        }

                        else if (line.Trim() == ")")
                        {
                            if (moreHtnSubtasks)
                            {
                                moreHtnSubtasks = false;
                            }
                            else
                            {
                                inHtnSubtasks = false;
                            }
                        }
                        else
                        {
                            // reading a task
                            ReadInitHTNTask(line, initHtnTasksByIDs);
                        }
                    }
                    else if (inHtn)
                    {
                        if (line.Contains(":subtasks") || line.Contains(":tasks") || line.Contains(":ordered-tasks") ||
                           line.Contains(":ordered-subtasks"))
                        {
                            inHtn = false;
                            inHtnSubtasks = true;
                            if (line.Trim().Contains("(and"))
                            {
                                moreHtnSubtasks = true;
                            }
                            else
                            {
                                ReadInitHTNTask(line, initHtnTasksByIDs);
                            }
                        }
                    }
                }
            }
            return conditions;
        }

        private void ReadInitHTNTask(string line, Dictionary<string, Task> initHtnTasksByIDs)
        {
            string[] items = line.Split('(', StringSplitOptions.TrimEntries | StringSplitOptions.RemoveEmptyEntries);
            int taskIndex = items.Length - 1;

            string taskID = null;

            if (taskIndex >= 0)
            {
                string taskString = items[taskIndex];
                string[] taskItems = taskString.Replace(")", "")
                    .Split(' ', StringSplitOptions.TrimEntries | StringSplitOptions.RemoveEmptyEntries);

                string taskName = taskItems[0];
                string[] parameters = taskItems[1..];

                Task goalTask = CreateTask(taskName, parameters, alltaskTypes, allConstants);

                initialHtnTasks.Add(goalTask);

                if (items.Length > 1)
                {
                    taskID = items[0].Trim();

                    initHtnTasksByIDs.Add(taskID, goalTask);
                }
            }
        }

        private void SortHtnTasks(Dictionary<string, Task> initHtnTasksByIDs, Dictionary<string, List<string>> orderingConstraints)
        {
            List<Task> sortedHTNTasks = new();
            Dictionary<string, int> numberOfPrecedingTasks = new();
            foreach (var task in initHtnTasksByIDs.Keys)
            {
                numberOfPrecedingTasks[task] = 0;
            }

            foreach (var task in orderingConstraints.Keys)
            {
                foreach (var succeedingTask in orderingConstraints[task])
                {
                    numberOfPrecedingTasks[succeedingTask]++;
                }
            }

            while (numberOfPrecedingTasks.Count > 0)
            {
                var firstTasks = numberOfPrecedingTasks.Keys.Where(x => numberOfPrecedingTasks[x] == 0);
                if (firstTasks.Count() != 1)
                {
                    throw new FormatException("Initial HTN tasks are not totally ordered.");
                }

                string nextTask = firstTasks.First();
                sortedHTNTasks.Add(initHtnTasksByIDs[nextTask]);
                numberOfPrecedingTasks.Remove(nextTask);

                if (orderingConstraints.TryGetValue(nextTask, out List<string> value))
                {
                    foreach (var succeedingTask in value)
                    {
                        numberOfPrecedingTasks[succeedingTask]--;
                    }
                }
            }

            if (sortedHTNTasks.Count != initialHtnTasks.Count)
            {
                throw new FormatException("Initial HTN tasks are not totally ordered.");
            }

            initialHtnTasks = sortedHTNTasks;
        }

        private void AddNewConstants(List<Constant> inputConstants, ref List<Constant> constants)
        {
            foreach (Constant c in inputConstants)
            {
                List<Constant> sameName = constants.Where(x => x.Name == c.Name).ToList();
                if (sameName == null || !sameName.Any()) 
                    constants.Add(c);
                //If my type is subset of previous type. We change it. 
                else
                {
                    foreach (Constant ct in sameName)
                    {
                        if (ct.Type.IsAncestorTo(c.Type))
                        {
                            ct.SetType(c.Type);
                        }
                        if (ct.Type.Name == "any") ct.SetType(c.Type); //We change the type to my type as we now know better what constant this is. 
                    }
                }
            }
        }

        //The line loks like this: (contentof pot1 contentpot1)
        private Term CreateStateCondition(string line, ref List<Constant> methodInfo, List<Constant> allConstants)
        {
            Tuple<Term, bool> tupleC = CreateCondition(line, ref methodInfo, allConstants);
            if (tupleC != null)
            {
                if (tupleC.Item2 == false) Console.WriteLine("Negative initial condition. Currently ignoring.");
                else
                {
                    Term c = tupleC.Item1;
                    return c;
                }
            }
            return null;
        }

        /// <summary>
        /// From a file with a solution creates actionInstance which is a term representing the action. 
        /// </summary>
        private Term CreateActionInstance(String s, List<ActionType> allActionTypes, List<Constant> allConstants)
        {
            s = s.Replace(")", "");
            string[] parts = s.Split(new char[] {' ', '\t'}, StringSplitOptions.RemoveEmptyEntries); 
            while (parts.Length > 0 && parts[0] == "")
            {
                parts = (string[])parts.Skip(1).ToArray();
            }
            if (parts.Length == 0)
            {

                return null;
            }
            else
            {
                string name = parts[0];
                string[] variables = (string[])parts.Skip(1).ToArray();
                Constant[] vars = new Constant[variables.Count()];
                ActionType m = FindActionType(allActionTypes, name, variables.Count());
                for (int i = 0; i < variables.Count(); i++)
                {
                    Constant c = FindConstant(variables[i], allConstants);
                    vars[i] = c;
                }
                Term actionInstance = new Term(name, vars);
                return actionInstance;
            }
        }
    }
}

