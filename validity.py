# Welcome to the Symbolic Logic Argument Validity Tester!
# To use this tool, please edit the lines below to test various arguments
# You may use any letters to represent variables.
# Use | for OR, & for AND, > for IMPLIES, ~ for NOT and = for EQUIVALENCE, () for specifying order. This can be changed via the "Single Character Constants" section if you like.
# Make sure there is no ambiguity of the order of operations!
# The validity of your argument will be printed to the console!


# Edit these lines:
premises = [
"~Q > ~R",
"~(P & Q)",
"~(~P & ~R)"
]
conclusion = "~(P = R)"

swap = False # Swap the premises and conclusion? (only works for 1 premise)


# End of user input


# Single Character Constants (MUST BE SINGLE CHARACTERS)
NOTCHAR = "~"
ANDCHAR = "&"
ORCHAR = "|"
IMPLCHAR = ">"
EQUIVCHAR = "="
OPENB = "("
CLOSEB = ")"

# Other Constants
LETTERS = [chr((x + 65) + 6*(x // 26)) for x in range(26 * 2)]
OPS = [NOTCHAR, ANDCHAR, ORCHAR, IMPLCHAR, EQUIVCHAR]


class Operator:
	ops = []
	def __init__(self, symbol, nOperands, evalFunc):
		self.symbol = symbol
		self.nOperands = nOperands
		self.evalFunc = evalFunc
		Operator.ops.append(self)

	@classmethod
	def makeOpKey(cls):
		key = {}
		for op in cls.ops:
			key[op.symbol] = op
		return key


NOT_OP = Operator(NOTCHAR, 1, lambda x: not x)
AND_OP = Operator(ANDCHAR, 2, lambda x,y: x and y)
OR_OP = Operator(ORCHAR, 2, lambda x,y: x or y)
IMP_OP = Operator(IMPLCHAR, 2, lambda x,y: not x or y)
EQUIV_OP = Operator(EQUIVCHAR, 2, lambda x,y: x == y)
VAR_OP = Operator("#", 1, None)
opKey = Operator.makeOpKey()


class Statement:
	def __init__(self, operation, operands):
		self.operation = operation
		self.operands = operands

	def evaluate(self, values):
		"""Return a boolean evaultion of the statement, given a dictionary of variable values"""
		if self.operation == VAR_OP:
			var = self.operands[0]
			return values[var]
		else:
			return(self.operation.evalFunc(*[operand.evaluate(values) for operand in self.operands]))

	def getAtomicVars(self):
		"""Return a SET of the atomic variables in a statement
		NOTE: Because it returns a set, there will be no duplicates"""
		if self.operation == VAR_OP:
			return set(self.operands)
		else:
			aVars = set([])
			for operand in self.operands:
				aVars = aVars.union(operand.getAtomicVars())
			return aVars

	def __repr__(self):
		if self.operation == VAR_OP:
			return self.operands[0]
		if len(self.operands) == 2:
			return f"{self.operation.symbol}({self.operands[0]}, {self.operands[1]})"
		else:
			return f"{self.operation.symbol}({self.operands[0]})"


def removeOuterParens(chars):
	"""Removes any redundant parentheses on the outer layer.
	Assumes non-empty set of chars"""
	while chars[0] == OPENB and chars[-1] == CLOSEB:
		p = 0
		earlyClose = False
		for i, char in enumerate(chars):
			if char == OPENB:
				p += 1
			elif char == CLOSEB:
				p -= 1
				if p == 0 and i != (len(chars) - 1):
					earlyClose = True
		if earlyClose:
			break
		else:
			chars.pop(0)
			chars.pop(-1)
	return chars


def parse(chars):
	"""RETURNS: a Statement object composed of a major operator and a recursive list of other Statement objects as the operands
	   This function will also catch many improper / ambiguous inputs"""
	assert(len(chars) > 0) # Empty string passed

	# Remove leading and trailing parens
	chars = removeOuterParens(chars)

	# Determine the operator and its operand(s)
	op = None
	operands = []
	currentlyInParens = False
	p = 0
	for i, currChar in enumerate(chars):
		if not currentlyInParens and currChar in OPS:
			assert(op == None) # Multiple operators found at same level
			if currChar == NOTCHAR:
				assert(len(operands) == 0) # Not_op found AFTER an operand
				op = NOT_OP
			else: # Double-edged operators
				assert(len(operands) == 1) # Invalid number of operands before operator
				op = opKey[currChar]
		elif not currentlyInParens and currChar in LETTERS:
			operands.append(currChar)
		elif currChar == OPENB:
			if currentlyInParens:
				p += 1
			else:
				currentlyInParens = True
				p = 1
				startOfOperand = i
		elif currChar == CLOSEB:
			assert(currentlyInParens) # Parentheses mismatch
			p -= 1
			if p == 0:
				operands.append(chars[startOfOperand:i+1])
				currentlyInParens = False
		else:
			assert(currentlyInParens) # Invalid symbol found

	if op == None:
		assert(len(operands)) == 1 # Invalid number of operands
		op = VAR_OP
	assert(p == 0) # Parentheses mismatch
	assert(len(operands) == op.nOperands) # Invalid number of operands found

	# Make recursive call
	if op == VAR_OP:
		parsedOperands = operands
	else:
		parsedOperands = []
		for operand in operands:
			parsedOperands.append(parse(operand))

	statement = Statement(op, parsedOperands)
	return statement


def addNegationParens(chars):
	"""Inserts parenthesis around all NOT statements to make parsing easier.
	EG: ~(A | B) & ~C   ------->    (~(A | B)) & (~C)
 	Note: this function will add parens to ALL instances of negation, even if there are already parens there"""
	i = 0
	p = 0
	while i < len(chars):
		if chars[i] == NOTCHAR:
			if chars[i+1] == OPENB:
				p = 1
				end = i + 2
				while end < len(chars):
					if chars[end] == OPENB:
						p += 1
					elif chars[end] == CLOSEB:
						p -= 1
						if p == 0:
							chars.insert(end, CLOSEB)
							chars.insert(i, OPENB)
					end += 1
			else:
				chars.insert(i, OPENB)
				chars.insert(i+3, CLOSEB)
			i += 1
		i += 1
	return chars


def removeWhitespace(string):
	return string.replace(" ", "")


def generatePermutations(setOfVars):
	"""Returns a list of dictionaries of variable:boolean pairs"""
	n = len(setOfVars)
	p = 2**n           # number of permutations (ie. returned list has length p)
	aVars = list(setOfVars)

	dicts = []
	for i in range(p):
		newDict = {}
		for varIndex in range(n):
			newDict[aVars[varIndex]] = (i // 2**varIndex) % 2 == 0  # Spooky math that works out!
		dicts.append(newDict)
	return dicts
 

def testValidity(premises, conclusion):
	# Parse input strings
	parsedPremises = []
	for premise in premises:
		parsedPremises.append(parse(addNegationParens(list(removeWhitespace(premise)))))
	parsedConclusion = parse(addNegationParens(list(removeWhitespace(conclusion))))

	# Find all atomic variables
	aVars = set([])
	for premise in parsedPremises:
		aVars = aVars.union(premise.getAtomicVars())
	aVars = aVars.union(parsedConclusion.getAtomicVars())

	# Generate all permutations for variable values
	perms = generatePermutations(aVars)

	# Evaluate and see if conclusion is ever false when all premises are true
	for perm in perms:
		if (parsedConclusion.evaluate(perm) == False):
			for premise in parsedPremises:
				if premise.evaluate(perm) == False:
					break
			else:
				return (f"This argument is INVALID. Consider the case: {perm}")
	return ("This argument is valid.")

if swap:
	assert(len(premises) == 1) # Attempted to swap conclusion with multiple premises...
	print(testValidity([conclusion], premises[0]))
else:
	print(testValidity(premises, conclusion))