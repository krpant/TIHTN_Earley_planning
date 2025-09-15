using System;

namespace PlanRecognitionExtension
{
    using PlanRecognitionNETF;
    internal class Task
    {
        public Task(TaskType taskType)
        {
            TaskType = taskType;
            TaskInstance = new Constant[taskType.NumOfVariables];
            for (int i = 0; i < taskType.NumOfVariables; i++)
            {
                TaskInstance[i] = new Constant(null, TaskType.TaskTerm.Variables[i].Type);
            }
        }

        public static bool SameTypeTasks(Task t1, Task t2)
        {
            return t1.TaskType.Equals(t2.TaskType);
        }

        public void SetVariable(int index, Constant constant)
        {
            if (index < 0 || index >= TaskInstance.Length)
            {
                throw new ArgumentOutOfRangeException("Invalid index.");
            }
            TaskInstance[index] = constant;
        }

        public override bool Equals(object obj)
        {
            return obj is Task task &&
                TaskType.Equals(task.TaskType) &&
                TaskInstancesEqual(task.TaskInstance); 
        }

        private bool TaskInstancesEqual(Constant[] taskInstance)
        {
            if (taskInstance == null || TaskInstance.Length != taskInstance.Length)
            {
                return false;
            }
            for (int i = 0; i < TaskInstance.Length; i++)
            {
                if (TaskInstance[i] != null && taskInstance[i] != null)
                {
                    if (TaskInstance[i].Name != taskInstance[i].Name)
                    {
                        return false;
                    }
                    if (TaskInstance[i].Type != null && taskInstance[i].Type != null)
                    {
                        if (!TaskInstance[i].Type.IsRelated(taskInstance[i].Type))
                        {
                            return false;
                        }
                    }
                    else if (TaskInstance[i].Type != null || taskInstance[i].Type != null)
                    {
                        return false;
                    }
                }
                else if (TaskInstance[i] != null || taskInstance[i] != null)
                {
                    return false;
                }
            }
            return true;
        }

        public override int GetHashCode()
        {
            int hashCode = -1393504293;
            hashCode = hashCode * -1521134295 + TaskType.GetHashCode();
            foreach (Constant constant in TaskInstance)
            {
                if (constant != null)
                {
                    hashCode = hashCode * -1521134295 + constant.GetHashCode();
                }
            }
            return hashCode;
        }

        public override string ToString()
        {
            string s = TaskType.Name + "(";

            for (int i = 0; i < TaskInstance.Length; i++)
            {
                Constant c = TaskInstance[i];
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

        public Task(TaskType taskType, Constant[] taskInstance)
        {
            TaskType = taskType;
            TaskInstance = taskInstance;
        }

        public TaskType TaskType { get; }
        public Constant[] TaskInstance { get; }

    }
}
