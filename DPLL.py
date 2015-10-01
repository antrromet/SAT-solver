# -*- coding: utf-8 -*-
import sys

finalModel = []

# Read the input file
inputFile = open(sys.argv[2])
numCNFs = -1
cnfs = []

# Evaluates the clause to either true or false
# 1 is True
# 0 is False
# -1 is Undefined : Unknown Literals present
def clauseValue(clause) :
    if (isinstance(clause, str)) :
        if (clause == "true") :
            return 1
        elif (clause == "false") :
            return 0
        else :
            return -1
    else :
        unknownLiteral = False
        for item in clause :
            if (item == "or") :
                continue
            # Find out if any unknown quantity is present in the clause or not
            if item != "true" or item != "false" :
                unknownLiteral = True
                break
        for item in clause :
            if (item == "or") :
                continue
            if item == "true" :
                return 1
        # If there is unknown literal then return -1, -1 indicates the clause value cannot be determined
        return -1 if unknownLiteral else 0

# Checks the clauses for satisfiability
def checkClauses (clauses, model) :
    # Updating clauses value with given model values
    for item in model :
        spl = item.split('=')
        literal = spl[0]
        value = spl[1]
        for i, clause in enumerate(clauses) :
            if (clause == literal) :
                clauses[i] = value
            elif (isinstance(clause, list)) :
                if (len(clause) == 2 and clause[1] == literal and clause[0] == "not") :
                    clauses[i] = "false" if value == "true" else "true"
                else :
                    for j, entity in enumerate(clause) :
                        if (entity == literal) :
                            clause[j] = value
                        elif (isinstance(entity, list) and len(entity) == 2 and entity[0] == "not" and entity[1] == literal) :
                            clause[j] = "false" if value == "true" else "true"
    foundUnknown = False
    for i, clause in enumerate(clauses) :
        value = clauseValue(clause)
        if (value == 0) :
            return 0
        elif (value == -1) :
            foundUnknown = True
        elif (value == 1) :
            clauses[i] = "true"
    # If false and unknown not found that means everything was true and hence return 1
    return -1 if foundUnknown else 1

def findClauses (cnf) :
    clauses = []
    # Base case : ~A
    if (len(cnf) == 2 and cnf[0] == "not") :
        clauses.append(cnf)
    elif (cnf[0] == "and") :
        for i, item in enumerate(cnf) :
            if i > 0 :
                clauses.append(item)
    else :
        clauses.append(cnf)
    return clauses
    
def findSymbols (cnf, symbols) :
    # Base case : ~A
    if (len(cnf) == 2 and cnf[0] == "not") :
        return [cnf[1]]
    for i, item in enumerate(cnf) :
        if (isinstance(item, str) and item != "or" and item != "and") :
            symbols.append(item)
        elif (isinstance(item, list) and item[0] == "not") :
            symbols.append(item[1])
        elif (isinstance(item, list)) :
            findSymbols(item, symbols)
    if (i+1 == len(cnf)) :
        symbols = list(set(symbols))
        symbols.sort()
        return symbols
        
def check (clauses, symbols, model):
    global finalModel
    finalModel = model
    value = checkClauses(clauses, model)
    # if every clause in clauses is true in model then return true
    if (value == 1) :
        finalModel = model
        return True
    # if some clause in clauses is false in model then return false
    elif (value == 0) :
        finalModel = model
        return False
    else :
        # P, value <- FIND-PURE-SYMBOLS(symbols, clauses, model)
        # Find pure symbol
        pureSymbol = ""
        pureSymbolValue = False
        for item in symbols :
            isItemInModel = False
            for modelItem in model :
                spl = modelItem.split('=')
                if (item == spl[0]) :
                    isItemInModel = True
                    break
            if isItemInModel :
                continue
            pureSymbol = item
            isPureSymbol = True
            symbolValues = []
            for clause in clauses :
                if (clause == item) :
                    symbolValues.append("true")
                elif (isinstance(clause, list) and len(clause) == 2 and clause[0] == "not" and clause[1] == item) :
                    symbolValues.append("false")
                elif (isinstance(clause, list)):
                    for entity in clause :
                        if (entity == item) :
                            symbolValues.append("true")
                        elif (isinstance(entity, list) and len(entity) == 2 and entity[0] == "not" and  entity[1] == item ) :
                            symbolValues.append("false")
            if (len(symbolValues) == 0)  :
                continue
            firstValue = symbolValues[0]
            for i,value in enumerate(symbolValues) :
                if (i>0) :
                    if value != firstValue :
                        isPureSymbol = False
                        break;
            if (isPureSymbol) :
                pureSymbolValue = firstValue
                break
            else :
                pureSymbol = ""
        # if P is non-null then return DPLL(clauses, symbols – P, model OR {P=value})
        if pureSymbol != "" :
            symbols.remove(pureSymbol)
            model.append(pureSymbol + "=" + (str(pureSymbolValue)).lower())
            return check(clauses, symbols, model)
        # P, value <- FIND-UNIT-CLAUSE(clauses, model)
        unitClause = ""
        unitClauseValue = ""
        for clause in clauses :
            if (len(clause) == 1) :
                for modelItem in model :
                    spl = modelItem.split('=')
                    if (clause == spl[0]) :
                        isItemInModel = True
                        break
                if isItemInModel :
                    continue
                else :
                    unitClause = clause
                    unitClauseValue = True
            elif (len(clause) == 2 and clause[0] == "not") :
                for modelItem in model :
                    spl = modelItem.split('=')
                    if (clause[1] == spl[0]) :
                        isItemInModel = True
                        break
                if isItemInModel :
                    continue
                else :
                    unitClause = clause[1]
                    unitClauseValue = False
        # if P is non-null then return DPLL(clauses, symbols – P, model ∪ {P=value})
        if unitClause != "" :
            symbols.remove(unitClause)
            model.append(unitClause + "=" + (str(unitClauseValue)).lower())
            return check(clauses, symbols, model)
        # P <- FIRST(symbols);
        # rest <- REST(symbols)
        firstSymbol = symbols[0]
        symbols.remove(firstSymbol)
        
        model1 = list(model)
        model2 = list(model)
        model1.append(firstSymbol +"=true")
        model2.append(firstSymbol +"=false")
        return (check(clauses, symbols, model1) or check(clauses, symbols, model2))
        
for line in inputFile:
    if (numCNFs > 0):
        cnfs.append(eval(line.strip()))
    else:
        numCNFs = int(line.strip())
outputFile = open('CNF_satisfiability.txt', 'w+')

# For each input check for satisfiability
for cnf in cnfs:
    for i in finalModel : del i
    satisfiability = check(findClauses(cnf), findSymbols(cnf, []), [])
    if satisfiability :
        finalModel.insert(0, "true")
        outputFile.write (str(finalModel)+ '\n')
    else :
        outputFile.write (str(["false"]) + '\n')
inputFile.close()
