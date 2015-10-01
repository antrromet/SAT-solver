# SAT-solver
A boolean satisfiability solver that takes a set of variables and connectives in CNF and returns either a satisfying assignment that would make the CNF sentence true or determines that no satisfying assignment is possible. In particular,its an implementation the DPLL algorithm.

###Input & Output format:
The input to the program should be a file consisting propositional sentences in CNF format represented in lists. Sample input file “CNF_sentences.txt” is provided. The number n in the first line indicates the number of input propositional sentences in the file. The next n lines contain one propositional sentence in CNF format per line. The variables are one character strings i.e. “A”, “B”...”Z”.

The command to run the program is in the following format:
```
python DPLL.py –i inputfilename
```
The output of the program is a file, named “CNF_satisfiability.txt”, containing n lines each containing a python list, where n is the number of CNF sentences in the input file. The first element in the python list would be either true or false indicating the boolean satisfiability of that particular input sentence. If the first element is true then the list must contain m additional elements, where m is the number of variables in the input sentence. For each variable, the corresponding element in the list indicates whether that variable is true or false to satisfy the boolean satisfiability of the input sentence.
