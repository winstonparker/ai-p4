# factorOperations.py
# -------------------
# Licensing Information:  You are free to use or extend these projects for
# educational purposes provided that (1) you do not distribute or publish
# solutions, (2) you retain this notice, and (3) you provide clear
# attribution to UC Berkeley, including a link to http://ai.berkeley.edu.
#
# Attribution Information: The Pacman AI projects were developed at UC Berkeley.
# The core projects and autograders were primarily created by John DeNero
# (denero@cs.berkeley.edu) and Dan Klein (klein@cs.berkeley.edu).
# Student side autograding was added by Brad Miller, Nick Hay, and
# Pieter Abbeel (pabbeel@cs.berkeley.edu).


from bayesNet import Factor
import operator as op
import util
import copy
import itertools

def joinFactorsByVariableWithCallTracking(callTrackingList=None):


    def joinFactorsByVariable(factors, joinVariable):
        """
        Input factors is a list of factors.
        Input joinVariable is the variable to join on.

        This function performs a check that the variable that is being joined on
        appears as an unconditioned variable in only one of the input factors.

        Then, it calls your joinFactors on all of the factors in factors that
        contain that variable.

        Returns a tuple of
        (factors not joined, resulting factor from joinFactors)
        """

        if not (callTrackingList is None):
            callTrackingList.append(('join', joinVariable))

        currentFactorsToJoin =    [factor for factor in factors if joinVariable in factor.variablesSet()]
        currentFactorsNotToJoin = [factor for factor in factors if joinVariable not in factor.variablesSet()]

        # typecheck portion
        numVariableOnLeft = len([factor for factor in currentFactorsToJoin if joinVariable in factor.unconditionedVariables()])
        if numVariableOnLeft > 1:
            print "Factor failed joinFactorsByVariable typecheck: ", factor
            raise ValueError, ("The joinBy variable can only appear in one factor as an \nunconditioned variable. \n" +
                               "joinVariable: " + str(joinVariable) + "\n" +
                               ", ".join(map(str, [factor.unconditionedVariables() for factor in currentFactorsToJoin])))

        joinedFactor = joinFactors(currentFactorsToJoin)
        return currentFactorsNotToJoin, joinedFactor

    return joinFactorsByVariable

joinFactorsByVariable = joinFactorsByVariableWithCallTracking()


def joinFactors(factors):
    """
    Question 3: Your join implementation

    Input factors is a list of factors.

    You should calculate the set of unconditioned variables and conditioned
    variables for the join of those factors.

    Return a new factor that has those variables and whose probability entries
    are product of the corresponding rows of the input factors.

    You may assume that the variableDomainsDict for all the input
    factors are the same, since they come from the same BayesNet.

    joinFactors will only allow unconditionedVariables to appear in
    one input factor (so their join is well defined).

    Hint: Factor methods that take an assignmentDict as input
    (such as getProbability and setProbability) can handle
    assignmentDicts that assign more variables than are in that factor.

    Useful functions:
    Factor.getAllPossibleAssignmentDicts
    Factor.getProbability
    Factor.setProbability
    Factor.unconditionedVariables
    Factor.conditionedVariables
    Factor.variableDomainsDict
    """

    # typecheck portion
    setsOfUnconditioned = [set(factor.unconditionedVariables()) for factor in factors]
    if len(factors) > 1:
        intersect = reduce(lambda x, y: x & y, setsOfUnconditioned)
        if len(intersect) > 0:
            print "Factor failed joinFactors typecheck: ", factor
            raise ValueError, ("unconditionedVariables can only appear in one factor. \n"
                    + "unconditionedVariables: " + str(intersect) +
                    "\nappear in more than one input factor.\n" +
                    "Input factors: \n" +
                    "\n".join(map(str, factors)))


    #do not remove above

    def getFactorByUnconditioned(var):
        ret = []
        for fac in factors:
            for unc in fac.unconditionedVariables():
                if unc in var:
                    ret.append(fac)
            # if fac.unconditionedVariables() == var:
            #     ret.append(fac)
        return ret

    un_var = set([])
    con_var = set([])
    dom_list = {}

    #go through the list of factors
    for fac in factors:
        # print fac
        if len(fac.conditionedVariables()) > 0:
            #get the factor for that conditioned variable
            con_fac = getFactorByUnconditioned(fac.conditionedVariables())
            if len(con_fac) > 0:
                for tfac in con_fac:
                    if len(tfac.conditionedVariables()) > 0:
                        #add fac's unconditionals to newFactor's unconditioned variables
                        for uncon in fac.unconditionedVariables():
                            if uncon not in un_var and uncon not in con_var:
                                un_var.add(uncon)
                        #go through con_fac's unconditioned variables and if it is in
                        #fac's conditionals then add it to newFac's unconditionals
                        for con_fac_uncon in tfac.unconditionedVariables():
                            if con_fac_uncon in fac.conditionedVariables():
                                if con_fac_uncon not in un_var and con_fac_uncon not in con_var:
                                    un_var.add(con_fac_uncon)
                        #go through fac's conditional variables and add it to newFac's conditionals
                        for fac_cons in fac.conditionedVariables():
                            if fac_cons not in con_var and fac_cons not in un_var:
                                con_var.add(fac_cons)
                        #go through con_fac's conditional variables and add them to newFac's conditionals
                        #if it is not in either newFac's unconditionals or conditionals
                        for con_fac_con in tfac.conditionedVariables():
                            if con_fac_con not in un_var and con_fac_con not in con_var:
                                con_var.add(con_fac_con)
                    else:
                        for uncon in fac.unconditionedVariables():
                            if uncon not in un_var and uncon not in con_var:
                                un_var.add(uncon)
                        for con_fac_uncon in tfac.unconditionedVariables():
                            if con_fac_uncon not in un_var and con_fac_uncon not in con_var:
                                un_var.add(con_fac_uncon)
            else:
                #conjoin the two factors
                for uncon in fac.unconditionedVariables():
                    if uncon not in un_var and uncon not in con_var:
                        un_var.add(uncon)
                for convars in fac.conditionedVariables():
                    if convars not in con_var and convars not in un_var:
                        con_var.add(convars)
        else:
            for con_fac_uncon in fac.unconditionedVariables():
                if con_fac_uncon not in un_var and con_fac_uncon not in con_var:
                    un_var.add(con_fac_uncon)
        dom_list.update(fac.variableDomainsDict())

    #build the new factor
    newFac = Factor(un_var, con_var, dom_list)

    pairs = [[]]
    for doms in newFac.variableDomainsDict().iterkeys():
        t = []
        for tmp in newFac.variableDomainsDict()[doms]:
            for i in pairs:
                t.append(i + [tmp])
        pairs = t

    #add the probabilities to the factor
    for dic in newFac.getAllPossibleAssignmentDicts():
        prob = 1
        for fac in factors:
            prob = prob * fac.getProbability(dic)
        newFac.setProbability(dic, prob)

    return newFac

def eliminateWithCallTracking(callTrackingList=None):

    def eliminate(factor, eliminationVariable):
        """
        Question 4: Your eliminate implementation

        Input factor is a single factor.
        Input eliminationVariable is the variable to eliminate from factor.
        eliminationVariable must be an unconditioned variable in factor.

        You should calculate the set of unconditioned variables and conditioned
        variables for the factor obtained by eliminating the variable
        eliminationVariable.

        Return a new factor where all of the rows mentioning
        eliminationVariable are summed with rows that match
        assignments on the other variables.

        Useful functions:
        Factor.getAllPossibleAssignmentDicts
        Factor.getProbability
        Factor.setProbability
        Factor.unconditionedVariables
        Factor.conditionedVariables
        Factor.variableDomainsDict
        """
        # autograder tracking -- don't remove
        if not (callTrackingList is None):
            callTrackingList.append(('eliminate', eliminationVariable))

        # typecheck portion
        if eliminationVariable not in factor.unconditionedVariables():
            print "Factor failed eliminate typecheck: ", factor
            raise ValueError, ("Elimination variable is not an unconditioned variable " \
                            + "in this factor\n" +
                            "eliminationVariable: " + str(eliminationVariable) + \
                            "\nunconditionedVariables:" + str(factor.unconditionedVariables()))

        if len(factor.unconditionedVariables()) == 1:
            print "Factor failed eliminate typecheck: ", factor
            raise ValueError, ("Factor has only one unconditioned variable, so you " \
                    + "can't eliminate \nthat variable.\n" + \
                    "eliminationVariable:" + str(eliminationVariable) + "\n" +\
                    "unconditionedVariables: " + str(factor.unconditionedVariables()))

        #dont remove from above

        #get data from old factor and make a new one
        temp2 = list(factor.unconditionedVariables())
        temp2.remove(eliminationVariable)
        finalremaining = list(temp2)
        newFactor = Factor(finalremaining, factor.conditionedVariables(),  factor.variableDomainsDict() )
        newList = list(factor.getAllPossibleAssignmentDicts())

        #remove dups from vars
        noDupes = []

        #remove elem var
        for diction in newList:
            diction.pop(eliminationVariable, None)

        for diction in newList:
            if diction not in noDupes:
                noDupes.append(diction)

        newList = noDupes

        #get all possible vals of emlim var and remove dups
        elimVals = [dict2[eliminationVariable] for dict2 in factor.getAllPossibleAssignmentDicts()]
        noDupes2 = []
        for val in elimVals:
            if val not in noDupes2:
                noDupes2.append(val)

        elimVals = noDupes2


        #for each new (lacking the elem var) dictionary , check the prob with a possible elem val and add them together
        for diction in newList:
            prob = 0
            for elimVal in elimVals:
                 temp = copy.deepcopy(diction)
                 temp[eliminationVariable] = elimVal
                 prob += factor.getProbability(temp)
            newFactor.setProbability(diction, prob)

        return newFactor
    return eliminate

eliminate = eliminateWithCallTracking()


def normalize(factor):
    """
    Question 5: Your normalize implementation

    Input factor is a single factor.

    The set of conditioned variables for the normalized factor consists
    of the input factor's conditioned variables as well as any of the
    input factor's unconditioned variables with exactly one entry in their
    domain.  Since there is only one entry in that variable's domain, we
    can either assume it was assigned as evidence to have only one variable
    in its domain, or it only had one entry in its domain to begin with.
    This blurs the distinction between evidence assignments and variables
    with single value domains, but that is alright since we have to assign
    variables that only have one value in their domain to that single value.

    Return a new factor where the sum of the all the probabilities in the table is 1.
    This should be a new factor, not a modification of this factor in place.

    If the sum of probabilities in the input factor is 0,
    you should return None.

    This is intended to be used at the end of a probabilistic inference query.
    Because of this, all variables that have more than one element in their
    domain are assumed to be unconditioned.
    There are more general implementations of normalize, but we will only
    implement this version.

    Useful functions:
    Factor.getAllPossibleAssignmentDicts
    Factor.getProbability
    Factor.setProbability
    Factor.unconditionedVariables
    Factor.conditionedVariables
    Factor.variableDomainsDict
    """

    # typecheck portion
    variableDomainsDict = factor.variableDomainsDict()
    for conditionedVariable in factor.conditionedVariables():
        if len(variableDomainsDict[conditionedVariable]) > 1:
            print "Factor failed normalize typecheck: ", factor
            raise ValueError, ("The factor to be normalized must have only one " + \
                            "assignment of the \n" + "conditional variables, " + \
                            "so that total probability will sum to 1\n" +
                            str(factor))

    "*** YOUR CODE HERE ***"


    # get data from old factor and make a new one


    conditional = list(factor.conditionedVariables())
    unconditional = []



    for var in factor.unconditionedVariables():
        multiple = False
        vals = [factor.getAllPossibleAssignmentDicts()[0][var]]

        for diction in factor.getAllPossibleAssignmentDicts():
            val = diction[var]
            if val not in vals:
                multiple = True
                break
        if multiple == False:
            conditional.append(var)
        else:
            unconditional.append(var)



    newFactor = Factor(unconditional, conditional, factor.variableDomainsDict())
    newList = list(factor.getAllPossibleAssignmentDicts())

    total = 0
    for diction in newList:
        temp = factor.getProbability(diction)
        total += temp

    for diction in newList:
        temp = factor.getProbability(diction)
        newFactor.setProbability(diction, temp / total)

    return newFactor
