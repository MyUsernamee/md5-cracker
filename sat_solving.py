# Recreate the md5 algorithm as a sat problem, then apply constraints to the input.
# This *should* dramatically reduce the possible space of answers and make it possible to output a smaller space
# Of possible solutions to search through.
from pysat.formula import CNF

# We are going to perform a "symbolic" computation on our input.
# We are going to make a list of "all possible names" (all strings with the characters a-zA-Z0-9_)
# Then we are going to make a "bit stream" of possible states for each bit.
# We can then "and" this with the character possibilities.
# This will limit our search space a bit, and might bring some insights.

test_hash = "2a21e2561359ebf2fb2d634ee7837a8e"
test_string = "Nvidia"

valid_chars = "abcdefghijklmnopqrstuvwxyz"
valid_chars += valid_chars.upper()
valid_chars += "0123456789_"
byte_possibilities = [set() for i in range(8)]

for char in valid_chars:
    # Convert to byte
    char_byte = char.encode('ascii')
    for bit_index in range(8):
        bit = (char_byte[0] & (0b1<<bit_index)) >> bit_index
        byte_possibilities[bit_index].add(bool(bit))

byte_possibilities
bit_string_possibilities =[]

class BOperand:
    def __and__(self, other):
        return BAnd(self, other)

    def __or__(self, other):
        return BOr(self, other)   

    def __invert__(self):
        return BNot(self)

    def cnf(self):
        # First nnf
        new_form = self._nnf()
        new_form = new_form._cnf()
        new_form = new_form._simplify()

        return new_form

    def simplify(self):
        return self._simplify()

    def _cnf(self):
        return self

    def _nnf(self):
        return self

    def _simplify(self):
        return self

    def _walk(self, method):
        method(self)

        for child in get_children():
            child._walk(method)

    def _wrap(ob):
        if isinstance(ob, bool):
            return BConst(ob)
        
        if not isinstance(ob, BOperand):
            raise Exception(f'{ob} is not a valid operand.')

        return ob

class BConst(BOperand):
    def __init__(self, value):
        self.value = value

    def __repr__(self):
        return str(self.value)

class BOp(BOperand):
    def __init__(self, lhs, rhs):
        
        lhs = BOperand._wrap(lhs)
        rhs = BOperand._wrap(rhs)

        self.lhs = lhs
        self.rhs = rhs 

        if isinstance(self.lhs, BOp) and not isinstance(self.rhs, BOp):
            self.flip() 

        if isinstance(self.lhs, BConst) and not isinstance(self.rhs, BConst):
            self.flip() 

    def _simplify(self):
        return self.__clas__(self.lhs._simplify(), self.rhs.simplify())

    def __repr__(self):
        return f'({repr(self.lhs)} {str(self)} {repr(self.rhs)})'

    def flip(self):
        tmp = self.rhs
        self.rhs = self.lhs
        self.lhs = tmp
    
    def distribute(self, op, cls):
        return cls(self.__class__(op, self.lhs), self.__class__(op, self.rhs)) 

    def _get_children(self):
        return [self.lhs, self.rhs]

    def _nnf(self):
        return self.__class__(self.lhs._nnf(), self.rhs._nnf())

    def _cnf(self):
        return self.__class__(self.lhs._cnf(), self.rhs._cnf())

class BNot(BOperand):
    def __init__(self, op):
        op = BOperand._wrap(op)
        self.op = op

    def __repr__(self):
        return f'-{repr(self.op)}'

    def _get_children(self):
        return [self.lhs, self.rhs]

    def _nnf(self):
        nnf_op = self.op._nnf()
        if isinstance(nnf_op, BNot):
            return nnf_op.op

        if isinstance(nnf_op, BOp):
            return nnf_op._get_nnf_form()(BNot(nnf_op.lhs)._nnf(), BNot(nnf_op.rhs)._nnf())

        return BNot(nnf_op)

    def _cnf(self):
        return BNot(self.op._cnf())

    def _simplify(self):
        if isinstance(self.op, BConst):
            return BConst(not self.op.value)
        return self

class BAnd(BOp):
    def __str__(self):
        return "&"

    def _get_nnf_form(self):
        return BOr

    def _eval(self, lhs, rhs):
        return lhs & rhs

    def _simplify(self):
        lhs = self.lhs._simplify()
        rhs = self.rhs._simplify()

        if isinstance(lhs, BConst) and isinstance(rhs, BConst):
            return BConst(lhs.value & rhs.value)

        if isinstance(lhs, BConst) and not isinstance(rhs, BConst):
            return rhs if lhs.value else BConst(False)
        if isinstance(rhs, BConst) and not isinstance(lhs, BConst):
            return lhs if rhs.value else BConst(False)

        return BAnd(lhs, rhs)

class BOr(BOp):
    def __str__(self):
        return "|"
    
    def _cnf(self):
        if isinstance(self.rhs, BAnd):
            return self.distribute(self.lhs._cnf(), BAnd)
        return self

    def _get_nnf_form(self):
        return BAnd

    def _eval(self, lhs, rhs):
        return lhs | rhs

    def _simplify(self):
        lhs = self.lhs._simplify()
        rhs = self.rhs._simplify()

        if isinstance(lhs, BConst) and isinstance(rhs, BConst):
            return BConst(lhs.value | rhs.value)

        if isinstance(lhs, BConst) and not isinstance(rhs, BConst):
            return rhs if not lhs.value else BConst(True)
        if isinstance(rhs, BConst) and not isinstance(lhs, BConst):
            return lhs if not rhs.value else BConst(True)

        return BOr(lhs, rhs)

class BitSymbol(BOperand):
    def get_id(self):
        return id(self) # Honestly, so I don't forget

    def __repr__(self):
        return str(id(self))

a = BitSymbol()
b = BitSymbol()
c = BitSymbol()

tests = ((a | c) & b) & (c | False)
tests.cnf()._simplify()

class BStream:
    def __init__(self, size=8, form=None):
        self.form = [BitSymbol() for i in range(size)] if not form else form # For every bit in the bit string, store the operation perform.
        # If this is a const, life is good. If not then we need to make a "new symbol"

    def __and__(self, other):
        new_form = None
        if isinstance(other, int):
            new_size = min(2**math.ceil(math.log2(other)), len(self.form))
            new_form = [None] * new_size

            # Convert other to binrary
            other = [(other & (0b1<<i)) >> i for i in range(new_size)]
            
            for (i, bit) in enumerate(other):
                new_form[i] = self.form[i] & bool(bit)
        elif isinstance(other, BStream):
            new_size = min(len(other.form), len(self.form))
            new_form = [None] * new_size

            for (i, bit) in enumerate(other.form[:new_size]):
                new_form[i] = self.form[i] & bit
        else:
            raise Exception(f'Unable to and {other}, and BStream')

        return BStream(len(new_form), form=new_form)

    def __or__(self, other):
        new_form = None
        if isinstance(other, int):
            new_size = max(2**math.ceil(math.log2(other)), len(self.form))
            new_form = [None] * new_size

            # Convert other to binrary
            other = [(other & (0b1<<i)) >> i for i in range(new_size)]

            for (i, bit) in enumerate(other):
                new_form[i] = self.form[i] | bool(bit)
        elif isinstance(other, BStream):
            new_size = max(len(other.form), len(self.form))
            new_form = [None] * new_size

            for i in range(new_size):
                other_bit = other.form[i] if i < len(other.form) else BConst(False)
                self_bit = self.form[i] if i < len(self.form) else BConst(False)
                new_form[i] = self_bit | other_bit
        else:
            raise Exception(f'Unable to and {other}, and BStream')

        return BStream(len(new_form), form=new_form)

    def __lshift__(self, other):
        new_form = [a for a in self.form]

        for i in range(other):
            new_form.insert(0, BConst(False))
        return BStream(len(self.form) + other, new_form)

    def __rshift__(self, other):
        new_form = [a for a in self.form]

        for i in range(other):
            new_form.append(BConst(False))
        return BStream(len(self.form) + other, new_form)

    def simplify(self):
        new_form = [a.simplify() for a in self.form]
        new_form = [a for a in new_form if not (isinstance(a, BConst) and a.value == False)]
        return BStream(form=new_form)

# Thank you: https://github.com/Utkarsh87/md5-hashing/blob/master/md5.py
import math

# This list maintains the amount by which to rotate the buffers during processing stage
rotate_by = [7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
			 5,  9, 14, 20, 5,  9, 14, 20, 5,  9, 14, 20, 5,  9, 14, 20,
			 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
			 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21]

# This list maintains the additive constant to be added in each processing step.
constants = [int(abs(math.sin(i+1)) * 4294967296) & 0xFFFFFFFF for i in range(64)]

# STEP 1: append padding bits s.t. the length is congruent to 448 modulo 512
# which is equivalent to saying 56 modulo 64.
# padding before adding the length of the original message is conventionally done as:
# pad a one followed by zeros to become congruent to 448 modulo 512(or 56 modulo 64).
def pad(msg):
	msg_len_in_bits = (8*len(msg)) & 0xffffffffffffffff
	msg.append(0x7f)

	while len(msg)%64 != 56:
		msg.append(0)

    # STEP 2: append a 64-bit version of the length of the length of the original message
    # in the unlikely event that the length of the message is greater than 2^64,
    # only the lower order 64 bits of the length are used.

    # sys.byteorder -> 'little'
	msg += msg_len_in_bits.to_bytes(8, byteorder='little') # little endian convention
	# to_bytes(8...) will return the lower order 64 bits(8 bytes) of the length.
	
	return msg


# STEP 3: initialise message digest buffer.
# MD buffer is 4 words A, B, C and D each of 32-bits.

init_MDBuffer = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476]

# UTILITY/HELPER FUNCTION:
def leftRotate(x, amount):
    x &= 0xFFFFFFFF
    return (x << amount | x >> (32-amount)) & 0xFFFFFFFF

a = BStream(8)
a.form
leftRotate(a, 3).simplify().form
pad([a])

# STEP 4: process the message in 16-word blocks
# Message block stored in buffers is processed in the follg general manner:
# A = B + rotate left by some amount<-(A + func(B, C, D) + additive constant + 1 of the 16 32-bit(4 byte) blocks converted to int form)

def from_little_bytes(bytes):
    flipped = list(reverse(bytes))
    proper = 

def processMessage(msg):
    
	init_temp = init_MDBuffer[:] # create copy of the buffer init constants to preserve them for when message has multiple 512-bit blocks
	
	# message length is a multiple of 512bits, but the processing is to be done separately for every 512-bit block.
	for offset in range(0, len(msg), 64):
		A, B, C, D = init_temp # have to initialise MD Buffer for every block
		block = msg[offset : offset+64] # create block to be processed
		# msg is processed as chunks of 16-words, hence, 16 such 32-bit chunks
		for i in range(64): # 1 pass through the loop processes some 32 bits out of the 512-bit block.
			if i < 16:
				# Round 1
				func = lambda b, c, d: (b & c) | (~b & d)
				# if b is true then ans is c, else d.
				index_func = lambda i: i

			elif i >= 16 and i < 32:
				# Round 2
				func = lambda b, c, d: (d & b) | (~d & c)
				# if d is true then ans is b, else c.
				index_func = lambda i: (5*i + 1)%16

			elif i >= 32 and i < 48:
				# Round 3
				func = lambda b, c, d: b ^ c ^ d
				# Parity of b, c, d
				index_func = lambda i: (3*i + 5)%16
			
			elif i >= 48 and i < 64:
				# Round 4
				func = lambda b, c, d: c ^ (b | ~d)
				index_func = lambda i: (7*i)%16

			F = func(B, C, D) # operate on MD Buffers B, C, D
			G = index_func(i) # select one of the 32-bit words from the 512-bit block of the original message to operate on.

			to_rotate = A + F + constants[i] + from_little_bytes(block[4*G : 4*G + 4], byteorder='little')
			newB = (B + leftRotate(to_rotate, rotate_by[i])) & 0xFFFFFFFF
				
			A, B, C, D = D, newB, B, C
			# rotate the contents of the 4 MD buffers by one every pass through the loop

		# Add the final output of the above stage to initial buffer states
		for i, val in enumerate([A, B, C, D]):
			init_temp[i] += val
			init_temp[i] &= 0xFFFFFFFF
		# The init_temp list now holds the MD(in the form of the 4 buffers A, B, C, D) of the 512-bit block of the message fed.

	
	# The same process is to be performed for every 512-bit block to get the final MD(message digest).

	
	# Construct the final message from the final states of the MD Buffers
	return sum(buffer_content<<(32*i) for i, buffer_content in enumerate(init_temp))


def MD_to_hex(digest):
	# takes MD from the processing stage, change its endian-ness and return it as 128-bit hex hash
	return digest


def md5(msg):
	msg = pad(msg)
	processed_msg = processMessage(msg)
	# processed_msg contains the integer value of the hash
	message_hash = MD_to_hex(processed_msg)
	print("Message Hash: ", message_hash)


if __name__ == '__main__':
	message = input()
	md5([BStream(8 * 8)])
