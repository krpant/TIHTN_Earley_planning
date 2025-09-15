Implementation of the Earley TIHTN planning technique and TIHTN planning benchmarks used for empirical evaluation presented in the paper *Pantůčková, Kristýna and Barták, Roman: Parsing-based Planner for Totally Ordered HTN Planning with Task Insertion* at the HPlan workshop at the ICAPS 2025 conference and at the ICTAI 2025 conference.

The domain Transport-TIHTN was created by modifying the HTN domain Transport from IPC 2020 (https://github.com/panda-planner-dev/ipc2020-domains).

Language and framework: C# 11.0, .NET 7.0

TIHTN planning with action insertion on the fly can be run as follows:
`EarleyPlanner.exe domain_file problem_file csv_result_file ti1 timeout_in_seconds anytime_solutions=y/n return_first_solution=y/n classical_planner_path` (e.g. `fast-downward.py`)

Optimal TIHTN planning can be run as follows:
`EarleyPlanner.exe domain_file problem_file csv_result_file ti2 timeout_in_seconds anytime_solutions=y/n return_first_solution=y/n classical_planner_path`

If `return_first_solution = y`, the planner will not keep searching for an optimal solution after the first solution is found.

If `anytime_solutions = y`, the planner will always try to compute all solutions that could have a better cost than those already found (may return more solutions with decreasing cost).

Example - an optimal search:
`EarleyPlanner.exe domain_file problem_file csv_result_file.csv ti2 300 y n FastDownward\fast-downward.py`

The program will write its output on the standard output and into the given csv file.
