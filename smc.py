#!/bin/python3

import sys
import re
import math

class Node:
    def __init__(self, name, type, width, ul, uh, sl, sh, ulc, uhc, slc, shc, hom, mh, vars):
        self.name = name
        self.type = type
        self.width = width
        self.ul = ul    # unsigned low
        self.uh = uh    # unsigned high
        self.sl = sl    # signed low
        self.sh = sh    # signed high
        self.ulc = ulc  # unsigned low cardinality
        self.uhc = uhc  # unsigned high cardinality
        self.slc = slc  # signed low cardinality
        self.shc = shc  # signed high cardinality
        self.hom = hom  # homogeneous
        self.mh = mh    # masked homogeneous
        self.vars = vars
    def printNode(self):
        print (self.name, self.type, self.width, self.ul, self.uh, self.sl, self.sh, self.ulc, self.uhc, self.slc, self.shc, self.hom, self.mh, self.vars)

class Bounds:
    def __init__(self, ula, uha, sla, sha, vars):
        self.ula = ula
        self.uha = uha
        self.sla = sla
        self.sha = sha
        self.vars = vars
    def printBound(self):
        print ("Unsigned Lower Bound: " + str(self.ula) + ", " + str(Log2(self.ula)) + " bits")
        print ("Unsigned Upper Bound: " + str(self.uha) + ", " + str(Log2(self.uha)) + " bits")
        print ("Signed Lower Bound: " + str(self.sla) + ", " + str(Log2(self.sla)) + " bits")
        print ("Signed Upper Bound: " + str(self.sha) + ", " + str(Log2(self.sha)) + " bits")


def mergeBounds(a, b):
    vars = list(a.vars) + list(set(b.vars) - set(a.vars))
    ula = uha = sla = sha = 1
    if not (set(a.vars).isdisjoint(b.vars)):
        if set(a.vars) == set(b.vars):
            if (a.ula < b.ula and a.uha < b.uha) or (a.ula > b.ula and a.uha > b.uha) :
                ula = min(a.ula, b.ula)
                uha = min(a.uha, b.uha)
            else:
                ula = max(a.ula, b.ula)
                uha = min(a.uha, b.uha)
            if (a.sla < b.sla and a.sha < b.sha) or (a.sla > b.sla and a.sha > b.sha) :
                sla = min(a.sla, b.sla)
                sha = min(a.sha, b.sha)
            else:
                sla = max(a.sla, b.sla)
                sha = min(a.sha, b.sha)
        elif set(a.vars).issubset(set(b.vars)):
            ula = b.ula
            uha = b.uha
            sla = b.sla
            sha = b.sha
        elif set(b.vars).issubset(set(a.vars)):
            ula = a.ula
            uha = a.uha
            sla = a.sla
            sha = a.sha
        else:
            ula = max(a.ula, b.ula)
            uha = a.uha * b.uha
            sla = max(a.sla, b.sla)
            sha = a.sha * b.sha
    else:
        ula = a.ula * b.ula
        uha = a.uha * b.uha
        sla = a.sla * b.sla
        sha = a.sha * b.sha
    return Bounds(ula, uha, sla, sha, vars)

def getULA(f, g):
    vars = list(f.vars) + list(set(g.vars) - set(f.vars))
    ula = 1
    for var in vars:
        ula = ula * getNode(var).ulc
    return ula
def getUHA(f, g):
    vars = list(f.vars) + list(set(g.vars) - set(f.vars))
    uha = 1
    for var in vars:
        uha = uha * getNode(var).uhc
    return uha
def getSLA(f, g):
    vars = list(f.vars) + list(set(g.vars) - set(f.vars))
    sla = 1
    for var in vars:
        sla = sla * getNode(var).slc
    return sla
def getSHA(f, g):
    vars = list(f.vars) + list(set(g.vars) - set(f.vars))
    sha = 1
    for var in vars:
        sha = sha * getNode(var).shc
    return sha

def isPermutation(f):
    return f.ulc == pow(2, f.width) and len(f.vars) == 1
def isConstant(f):
    return f.type == 'bvconst' or f.ul == f.uh or f.sl == f.sh
def isCommon(f, g):
    return (not set(f.vars).isdisjoint(g.vars))
def isPowerOfTwo(n):
    return (math.ceil(Log2(n)) == math.floor(Log2(n)))
def isOddU(f):
    return f.ul % 2 == 1 and isConstant(f)
def isOddS(f):
    return f.sl % 2 == 1 and isConstant(f)
def isVars(name):
    global nodes
    for node in nodes:
        if name == node.name:
            return True
    return False
def bits_to_signed(str,bits):
    value = int(str,16)
    if value & (1 << (bits-1)):
        value -= 1 << bits
    return value
def maxNumOfBitsSetU(f):
    if isConstant(f):
        return numOfBitsSet(f.ul)
    return nextPowerOf2(f.uh)
def minNumOfBitsSetU(f):
    if isConstant(f):
        return numOfBitsSet(f.ul)
    if f.ul > 0:
        return 1
    return 0
def numOfBitsSet(n):
    count = 0
    while(n):
        count += n & 1
        n >>= 1
    return count
def nextPowerOf2(n):
    count = 0 
    if (n and not(n & (n - 1))):
        return n 
    while( n != 0):
        n >>= 1
        count += 1
    return count
def max_or(x, y):
    h = max(x, y)
    l = min(x, y)
    return h | (2**nextPowerOf2(l)-1)
def min_xorU(f, c):
    if c < f.ul:
        return f.ul & ~(2**nextPowerOf2(c)-1)
    if f.uh < c:
        return c & ~(2**nextPowerOf2(f.uh)-1)
    return 0
def input_bits(f, g):
    return f.width * len(f.vars) + g.width * len(list(set(g.vars) - set(f.vars)))
def input_count(f, g):
    return 2**input_bits(f, g)
def ldU(f):
    if f.hom:
        return input_count(f, f)/ f.uhc
    else:
        return 1
def hdU(f):
    if f.hom:
        return input_count(f, f) / f.ulc
    else:
        return input_count(f, f) - f.ulc + 1
def ldS(f):
    if f.hom:
        return input_count(f, f)/ f.shc
    else:
        return 1
def hdS(f):
    if f.hom:
        return input_count(f, f) / f.slc
    else:
        return input_count(f, f) - f.slc + 1
    
def Log2(x): 
    if x == 0:
        raise Exception('%f should not be zero', x)
  
    return math.log10(x)/math.log10(2)

def getNode(name):
    global nodes, temps
    if re.search(r'\#x([0-9a-f]+)', name):
        match = re.search(r'\#x([0-9a-f]+)', name)
        width = len(match.group(1)) * 4
        unsigned_num = int(match.group(1), 16)
        signed_num = bits_to_signed(match.group(1),16)
        return Node(name, 'bvconst', width, unsigned_num, unsigned_num, signed_num, signed_num, 1, 1, 1, 1, True, True, [])
    elif re.search(r'\#b[0-1]+', name):
        match = re.search(r'\#b([0-1]+)', name)
        width = len(match.group(1))
        unsigned_num = int(match.group(1), 2)
        signed_num = bits_to_signed(match.group(1),2)
        return Node(name, 'bvconst', width, unsigned_num, unsigned_num, signed_num, signed_num, 1, 1, 1, 1, True, True, [])
    elif re.search(r'temp([0-9]+)', name):
        for node in temps:
            #print(node.name, node.type)
            if node.name == name:
                return node
    else:
        for node in nodes:
            if node.name == name:
                return node
    raise Exception('Node %s not found ', name)

def eq_tok(var1, var2, cnt):
    f = getNode(var1)
    g = getNode(var2)
    if (f.width != g.width):
        raise Exception('Width must match')
    
    if f.uh < g.ul or g.uh < f.ul:
        raise Exception('unsatisfiable')
    
    vars = list(f.vars) + list(set(g.vars) - set(f.vars))
    if isConstant(f) and isConstant(g) and f.ul == g.ul:
        return Node('temp'+str(cnt), 'bveq_op', f.width, 0, 0, 0, 0, 1, 1, 1, 1, True, True, [f.name, g.name])
    if isCommon(f, g):
        ula = uha = sla = sha = input_bits(f, g)

        bounds.append(Bounds(ula, uha, sla, sha, vars))
        return Node('temp'+str(cnt), 'bveq_op', f.width, 0, 0, 0, 0, 1, 1, 1, 1, True, True, [f.name, g.name])
    leq = max(f.ul, g.ul)
    heq = min(f.uh, g.uh)
    minlhit = f.ulc - max(f.uh - heq, leq - f.ul)
    minlhit = min(minlhit, heq - leq + 1)
    minrhit = g.ulc - max(g.uh - heq, leq - g.ul)
    minrhit = min(minrhit, heq - leq + 1)
    inter = max(1, minlhit + minrhit - (heq - leq + 1))
    ic = input_count(f, g)
    ula = max(1, min(inter * ldU(f) * ldU(g), ic))
    uha = min(inter * hdU(f) * hdU(g), ic)

    bounds.append(Bounds(ula, uha, ula, uha, vars))
    return Node('temp'+str(cnt), 'bveq_op', f.width, 0, 0, 0, 0, 1, 1, 1, 1, True, True, [f.name, g.name])

def noteq_tok(parse, cnt):
    f = getNode(getNode(parse[1]).vars[0])
    g = getNode(getNode(parse[1]).vars[1])
    if (f.width != g.width):
        raise Exception('Width must match')
    
    if isConstant(f) and isConstant(g) and f.ul == g.ul:
        raise Exception('unsatisfiable')
    
    bounds.pop()
    vars = list(f.vars) + list(set(g.vars) - set(f.vars))
    if f.uh < g.ul or g.uh < f.ul:
        ula = sla = 0
        uha = sha = 0
        bounds.append(Bounds(ula, uha, sla, sha, vars))
        return Node('temp'+str(cnt), 'bvnoteq_op', f.width, 0, 0, 0, 0, 1, 1, 1, 1, True, True, vars)
    if isCommon(f, g):
        ula = uha = sla = sha = input_bits(f, g)
        bounds.append(Bounds(ula, uha, sla, sha, vars))
        return Node('temp'+str(cnt), 'bvnoteq_op', f.width, 0, 0, 0, 0, 1, 1, 1, 1, True, True, vars)
    leq = max(f.ul, g.ul)
    heq = min(f.uh, g.uh)
    ula = max(1, input_count(f, g) - (heq - leq + 1) * hdU(f) * hdU(g))
    uha = input_count(f, g)
    sla = ula
    sha = uha
    bounds.append(Bounds(ula, uha, sla, sha, vars))
    return Node('temp'+str(cnt), 'bvnoteq_op', f.width, 0, 0, 0, 0, 1, 1, 1, 1, True, True, vars)

def bvult_tok(var1, var2, cnt):
    f = getNode(var1)
    g = getNode(var2)
    if (f.width != g.width):
        raise Exception('Width must match')
    global isUnsigned, isSigned
    if f.ul >= g.uh:
        isUnsigned = False
        print ('Unsigned representation unsatisfiable')
    if f.sl >= g.sh:
        isSigned = False
        print ('Signed representation unsatisfiable')
     
    vars = list(f.vars) + list(set(g.vars) - set(f.vars))
    if f.uh < g.ul:
        ula = f.ulc * g.ulc
        sla = f.slc * g.slc
        uha = f.uhc * g.uhc
        sha = f.shc * g.shc
        bounds.append(Bounds(ula, uha, sla, sha, vars))
        return Node('temp'+str(cnt), 'bvult_op', f.width, 0, 0, 0, 0, 1, 1, 1, 1, True, True, [f.name, g.name])
    wcRange = g.ul - (f.uh - f.ulc + 1)
    if wcRange >= 1:
        accepted = min(wcRange*ldU(f), input_count(f, f))
    elif isCommon(f, g):
        accepted = 1
    else:
        accepted = ldU(f)
    
    ula = accepted * pow(2, g.width * len(list(set(g.vars) - set(f.vars))))
    uha = input_count(f, g)
    sla = ula
    sha = uha
    bounds.append(Bounds(ula, uha, sla, sha, vars))

    if isConstant(g) and f.uh > g.ul:
        f.uh = g.ul

    return Node('temp'+str(cnt), 'bvult_op', f.width, 0, 0, 0, 0, 1, 1, 1, 1, True, True, [f.name, g.name])

def bvugt_tok(var1, var2, cnt):
    f = getNode(var1)
    g = getNode(var2)
    if (f.width != g.width):
        raise Exception('Width must match')
    global isUnsigned, isSigned
    if f.uh <= g.ul:
        isUnsigned = False
        print ('Unsigned representation unsatisfiable')
    if f.sh <= g.sl:
        isSigned = False
        print ('Unsigned representation unsatisfiable')
    
    vars = list(f.vars) + list(set(g.vars) - set(f.vars))
    if f.ul > g.uh:
        ula = sla = 0
        uha = sha = 0
        bounds.append(Bounds(ula, uha, sla, sha, vars))
        return Node('temp'+str(cnt), 'bvugt_op', f.width, 0, 0, 0, 0, 1, 1, 1, 1, True, True, [f.name, g.name])
    wcRange = f.ul + f.ulc - g.uh - 1
    if wcRange >= 1:
        accepted = min(wcRange*ldU(f), input_count(f, f))
    elif isCommon(f, g):
        accepted = 1
    else:
        accepted = ldU(f)
    
    ula = accepted * pow(2, g.width * len(list(set(g.vars) - set(f.vars))))
    uha = input_count(f, g)
    sla = ula
    sha = uha
    bounds.append(Bounds(ula, uha, sla, sha, vars))

    return Node('temp'+str(cnt), 'bvugt_op', f.width, 0, 0, 0, 0, 1, 1, 1, 1, True, True, [f.name, g.name])

def bvslt_tok(var1, var2, cnt):
    f = getNode(var1)
    g = getNode(var2)
    if (f.width != g.width):
        raise Exception('Width must match')
    global isUnsigned, isSigned
    if f.ul > g.uh:
        isUnsigned = False
        print ('Unsigned representation unsatisfiable')
    if f.sl > g.sh:
        isSigned = False
        print ('Signed representation unsatisfiable')
    
    vars = list(f.vars) + list(set(g.vars) - set(f.vars))
    
    if isConstant(f) and isConstant(g):
        return Node('temp'+str(cnt), 'bvslt_op', f.width, 0, 0, 0, 0, 0, 0, 0, 0, True, True, [f.name, g.name])
    elif isConstant(f):
        uc = f.uh
        if g.uh > uc:
            if abs(uc - g.ul + 1) < g.uhc:
                g.uhc = abs(uc - g.ul + 1)
            if abs(uc - g.ul + 1) < g.ulc:
                g.ulc = g.ulc - abs(g.uh - uc)
                if g.ulc < 0:
                    g.ulc = 1
            g.uh = uc
        ula = g.ulc
        sc = f.sh
        if g.sh > sc:
            if abs(sc - g.sl + 1) < g.shc:
                g.shc = abs(sc - g.sl + 1)
            if abs(sc - g.sl + 1) < g.slc:
                g.slc = g.slc - abs(g.sh - sc)
                if g.slc < 0:
                    g.slc = 1
            g.sh = sc
        sla = g.ulc
    elif isConstant(g):
        uc = g.uh
        if f.uh > uc:
            if abs(uc - f.ul + 1) < f.uhc:
                f.uhc = abs(uc - f.ul + 1)
            if abs(uc - f.ul + 1) < f.ulc:
                f.ulc = f.ulc - abs(f.uh - uc)
                if f.ulc < 0:
                    f.ulc = 1
            f.uh = g.uh
        ula = f.ulc
        sc = g.sh
        if f.sh > sc:
            if abs(sc - f.sl + 1) < f.shc:
                f.shc = abs(sc - f.sl + 1)
            if abs(sc - f.sl + 1) < f.slc:
                f.slc = f.slc - abs(f.sh - sc)
                if f.slc < 0:
                    f.slc = 1
            f.sh = sc
        sla = f.slc
    else:
        if f.uh <= g.ul:
            ula = getULA(f, g)
            uha = getUHA(f, g)
        else:
            wcRange = g.ul - (f.uh - f.ulc)
            if wcRange >= 1:
                accepted = min(wcRange*ldU(f), input_count(f, f))
            elif isCommon(f, g):
                accepted = 1
            else:
                accepted = ldU(f)
        
            ula = accepted * pow(2, g.width * len(list(set(g.vars) - set(f.vars))))
        
        if f.sh <= g.sl :
            sla = getULA(f, g)
            sha = getUHA(f, g)
        else:
            wcRange = g.sl - (f.sh - f.slc)
            if wcRange >= 1:
                accepted = min(wcRange*ldS(f), input_count(f, f))
            elif isCommon(f, g):
                accepted = 1
            else:
                accepted = ldS(f)
    
            sla = accepted * pow(2, g.width * len(list(set(g.vars) - set(f.vars))))

    uha = getUHA(f, g)
    sha = getSHA(f, g)
    bounds.append(Bounds(ula, uha, sla, sha, vars))

    return Node('temp'+str(cnt), 'bvslt_op', f.width, 0, 0, 0, 0, ula, uha, sla, sha, True, True, [f.name, g.name])

def bvsgt_tok(var1, var2, cnt):
    f = getNode(var1)
    g = getNode(var2)
    if (f.width != g.width):
        raise Exception('Width must match')
    global isUnsigned, isSigned
    if f.uh < g.ul:
        isUnsigned = False
        print ('Unsigned representation unsatisfiable')
    if f.sh < g.sl:
        isSigned = False
        print ('Signed representation unsatisfiable')
    
    vars = list(f.vars) + list(set(g.vars) - set(f.vars))

    if isConstant(f) and isConstant(g):
        return Node('temp'+str(cnt), 'bvsgt_op', f.width, 0, 0, 0, 0, 1, 1, 1, 1, True, True, [f.name, g.name])
    elif isConstant(f):
        uc = f.uh
        if g.ul < uc:
            if abs(g.uh - uc + 1) < g.uhc:
                g.uhc = abs(g.uh - uc + 1)
            if abs(g.uh - uc + 1) < g.ulc:
                g.ulc = g.ulc - abs(uc - g.ul)
                if g.ulc < 0:
                    g.ulc = 1
            g.ul = uc
        ula = g.ulc
        sc = f.sh
        if g.sl < sc:
            if abs(g.sh - sc + 1) < g.shc:
                g.shc = abs(g.sh - sc + 1)
            if abs(g.sh - sc + 1) < g.slc:
                g.slc = g.slc - abs(sc - g.sl)
                if g.slc < 0:
                    g.slc = 1
            g.sl = sc
        sla = g.slc
    elif isConstant(g):
        uc = g.uh
        if f.ul < uc:
            if abs(f.uh - uc + 1) < f.uhc:
                f.uhc = abs(f.uh - uc + 1)
            if abs(f.uh - uc + 1) < f.ulc:
                f.ulc = f.ulc - abs(uc - f.ul)
                if f.ulc < 0:
                    f.ulc = 1
            f.ul = uc
        ula = f.ulc
        sc = g.sh
        if f.sl < sc:
            if abs(f.sh - sc + 1) < f.shc:
                f.shc = abs(f.sh - sc + 1)
            if abs(f.sh - sc + 1) < f.slc:
                f.slc = f.slc - abs(sc - f.sl)
                if f.slc < 0:
                    f.slc = 1
            f.sl = sc
        sla = f.shc
    else:
        if f.ul >= g.uh:
            ula = getULA(f, g)
            uha = getUHA(f, g)
        else:
            wcRange = f.ul - (g.uh - f.ulc)
            if wcRange >= 1:
                accepted = min(wcRange*ldU(f), input_count(f, f))
            elif isCommon(f, g):
                accepted = 1
            else:
                accepted = ldU(f)
        
            ula = accepted * pow(2, g.width * len(list(set(g.vars) - set(f.vars))))

        if f.sl > g.sh:
            sla = input_count(f, g)
            sha = input_count(f, g)
        else:
            wcRange = f.sl - (g.sh - f.slc)
            if wcRange >= 1:
                accepted = min(wcRange*ldS(f), input_count(f, f))
            elif isCommon(f, g):
                accepted = 1
            else:
                accepted = ldS(f)
        
            sla = accepted * pow(2, g.width * len(list(set(g.vars) - set(f.vars))))

    uha = getUHA(f, g)
    sha = getSHA(f, g)
    bounds.append(Bounds(ula, uha, sla, sha, vars))

    return Node('temp'+str(cnt), 'bvsgt_op', f.width, 0, 0, 0, 0, ula, uha, sla, sha, True, True, [f.name, g.name])

def bvsle_tok(var1, var2, cnt):
    f = getNode(var1)
    g = getNode(var2)
    if (f.width != g.width):
        raise Exception('Width must match')
    global isUnsigned, isSigned
    if f.ul > g.uh:
        isUnsigned = False
        print ('Unsigned representation unsatisfiable')
    if f.sl > g.sh:
        isSigned = False
        print ('Signed representation unsatisfiable')
    
    vars = list(f.vars) + list(set(g.vars) - set(f.vars))
    
    if isConstant(f) and isConstant(g):
        return Node('temp'+str(cnt), 'bvsle_op', f.width, 0, 0, 0, 0, 1, 1, 1, 1, True, True, [f.name, g.name])
    elif isConstant(f):
        uc = f.uh
        if g.uh > uc:
            if abs(uc - g.ul + 1) < g.uhc:
                g.uhc = abs(uc - g.ul + 1)
            if abs(uc - g.ul + 1) < g.ulc:
                g.ulc = g.ulc - abs(g.uh - uc)
                if g.ulc < 0:
                    g.ulc = 1
            g.uh = uc
        ula = g.ulc
        sc = f.sh
        if g.sh > sc:
            if abs(sc - g.sl + 1) < g.shc:
                g.shc = abs(sc - g.sl + 1)
            if abs(sc - g.sl + 1) < g.slc:
                g.slc = g.slc - abs(g.sh - sc)
                if g.slc < 0:
                    g.slc = 1
            g.sh = sc
        sla = g.ulc
    elif isConstant(g):
        uc = g.uh
        if f.uh > uc:
            if abs(uc - f.ul + 1) < f.uhc:
                f.uhc = abs(uc - f.ul + 1)
            if abs(uc - f.ul + 1) < f.ulc:
                f.ulc = f.ulc - abs(f.uh - uc)
                if f.ulc < 0:
                    f.ulc = 1
            f.uh = g.uh
        ula = f.ulc
        sc = g.sh
        if f.sh > sc:
            if abs(sc - f.sl + 1) < f.shc:
                f.shc = abs(sc - f.sl + 1)
            if abs(sc - f.sl + 1) < f.slc:
                f.slc = f.slc - abs(f.sh - sc)
                if f.slc < 0:
                    f.slc = 1
            f.sh = sc
        sla = f.slc
    else:
        if f.uh <= g.ul:
            ula = getULA(f, g)
            uha = getUHA(f, g)
        else:
            wcRange = g.ul - (f.uh - f.ulc)
            if wcRange >= 1:
                accepted = min(wcRange*ldU(f), input_count(f, f))
            elif isCommon(f, g):
                accepted = 1
            else:
                accepted = ldU(f)
        
            ula = accepted * pow(2, g.width * len(list(set(g.vars) - set(f.vars))))
        
        if f.sh <= g.sl :
            sla = getULA(f, g)
            sha = getUHA(f, g)
        else:
            wcRange = g.sl - (f.sh - f.slc)
            if wcRange >= 1:
                accepted = min(wcRange*ldS(f), input_count(f, f))
            elif isCommon(f, g):
                accepted = 1
            else:
                accepted = ldS(f)
    
            sla = accepted * pow(2, g.width * len(list(set(g.vars) - set(f.vars))))

    uha = getUHA(f, g)
    sha = getSHA(f, g)
    bounds.append(Bounds(ula, uha, sla, sha, vars))

    return Node('temp'+str(cnt), 'bvsle_op', f.width, 0, 0, 0, 0, ula, uha, sla, sha, True, True, [f.name, g.name])

def bvsge_tok(var1, var2, cnt):
    f = getNode(var1)
    g = getNode(var2)
    if (f.width != g.width):
        raise Exception('Width must match')
    global isUnsigned, isSigned
    if f.uh < g.ul:
        isUnsigned = False
        print ('Unsigned representation unsatisfiable')
    if f.sh < g.sl:
        isSigned = False
        print ('Signed representation unsatisfiable')
    
    vars = list(f.vars) + list(set(g.vars) - set(f.vars))

    if isConstant(f) and isConstant(g):
        return Node('temp'+str(cnt), 'bvsge_op', f.width, 0, 0, 0, 0, 1, 1, 1, 1, True, True, [f.name, g.name])
    elif isConstant(f):
        uc = f.uh
        if g.ul < uc:
            if abs(g.uh - uc + 1) < g.uhc:
                g.uhc = abs(g.uh - uc + 1)
            if abs(g.uh - uc + 1) < g.ulc:
                g.ulc = g.ulc - abs(uc - g.ul)
                if g.ulc < 0:
                    g.ulc = 1
            g.ul = uc
        ula = g.ulc
        sc = f.sh
        if g.sl < sc:
            if abs(g.sh - sc + 1) < g.shc:
                g.shc = abs(g.sh - sc + 1)
            if abs(g.sh - sc + 1) < g.slc:
                g.slc = g.slc - abs(sc - g.sl)
                if g.slc < 0:
                    g.slc = 1
            g.sl = sc
        sla = g.slc
    elif isConstant(g):
        uc = g.uh
        if f.ul < uc:
            if abs(f.uh - uc + 1) < f.uhc:
                f.uhc = abs(f.uh - uc + 1)
            if abs(f.uh - uc + 1) < f.ulc:
                f.ulc = f.ulc - abs(uc - f.ul)
                if f.ulc < 0:
                    f.ulc = 1
            f.ul = uc
        ula = f.ulc
        sc = g.sh
        if f.sl < sc:
            if abs(f.sh - sc + 1) < f.shc:
                f.shc = abs(f.sh - sc + 1)
            if abs(f.sh - sc + 1) < f.slc:
                f.slc = f.slc - abs(sc - f.sl)
                if f.slc < 0:
                    f.slc = 1
            f.sl = sc
        sla = f.shc
    else:
        if f.ul >= g.uh:
            ula = getULA(f, g)
            uha = getUHA(f, g)
        else:
            wcRange = f.ul - (g.uh - f.ulc)
            if wcRange >= 1:
                accepted = min(wcRange*ldU(f), input_count(f, f))
            elif isCommon(f, g):
                accepted = 1
            else:
                accepted = ldU(f)
        
            ula = accepted * pow(2, g.width * len(list(set(g.vars) - set(f.vars))))

        if f.sl > g.sh:
            sla = input_count(f, g)
            sha = input_count(f, g)
        else:
            wcRange = f.sl - (g.sh - f.slc)
            if wcRange >= 1:
                accepted = min(wcRange*ldS(f), input_count(f, f))
            elif isCommon(f, g):
                accepted = 1
            else:
                accepted = ldS(f)
        
            sla = accepted * pow(2, g.width * len(list(set(g.vars) - set(f.vars))))

    uha = getUHA(f, g)
    sha = getSHA(f, g)
    bounds.append(Bounds(ula, uha, sla, sha, vars))

    return Node('temp'+str(cnt), 'bvsge_op', f.width, 0, 0, 0, 0, 1, 1, 1, 1, True, True, [f.name, g.name])

def bvadd_tok(var1, var2, cnt):
    f = getNode(var1)
    g = getNode(var2)
    if (f.width != g.width):
        raise Exception('Width must match')

    umax = pow(2, f.width) - 1
    umin = 0
    smax = pow(2, f.width-1) - 1
    smin = -smax - 1
    tc = pow(2, f.width)
     
    vars = list(f.vars) + list(set(g.vars) - set(f.vars))
    
    if f.uh + g.uh > umax:
        if isConstant(f) and isConstant(g):
            ul = uh = f.ul + g.ul - 2**f.width
        else:
            ul = umin
            uh = umax
    else:
        ul = f.ul + g.ul
        uh = f.uh + g.uh

    if f.sl + g.sl < smin or f.sh + g.sh > smax:
        sl = smin
        sh = smax
    else:
        sl = f.sl + g.sl
        sh = f.sh + g.sh

    ulc = min(f.ulc+g.ulc-1, abs(uh-ul))
    slc = min(f.slc+g.slc-1, abs(sh-sl))

    if isCommon(f,g):
        ulc = 1
        slc = 1

    uhc = min(f.uhc * g.uhc, abs(uh-ul))
    shc = min(f.shc * g.shc, abs(sh-sl))

    mh = (isPermutation(f) and isConstant(g)) or (isConstant(f) and isPermutation(g))

    if mh:
        ulc = uhc
        slc = shc
    hom = (f.hom and isConstant(g)) or (isConstant(f) and g.hom) or (not isCommon(f,g) and isPermutation(f) and isPermutation(g)) or mh

    return Node('temp'+str(cnt), 'bvadd_op', f.width, ul, uh, sl, sh, ulc, uhc, slc, shc, hom, mh, vars)

def bvsubtract_tok(var1, var2, cnt):
    f = getNode(var1)
    g = getNode(var2)
    if (f.width != g.width):
        raise Exception('Width must match')
    
    umax = pow(2, f.width) - 1
    umin = 0
    smax = pow(2, f.width-1) - 1
    smin = -smax - 1
    tc = pow(2, f.width)
    
    vars = list(f.vars) + list(set(g.vars) - set(f.vars))
    
    if f.ul < g.uh :
        if isConstant(f) and isConstant(g):
            ul = uh = f.ul - g.ul + 2**f.width
        else:
            ul = umin
            uh = umax
    else:
        ul = f.ul - g.uh
        uh = f.uh - g.ul

    if f.sl - g.sh < smin or f.sh - g.sl > smax:
        sl = smin
        sh = smax
    else:
        sl = f.sl - g.sh
        sh = f.sh - g.sl

    ulc = min(f.ulc+g.ulc-1, tc)
    slc = min(f.slc+g.slc-1, tc)

    if isCommon(f,g):
        ulc = 1
        slc = 1

    uhc = min(f.uhc * g.uhc, tc)
    shc = min(f.shc * g.uhc, tc)
  
    mh = (isPermutation(f) and isConstant(g)) or (isConstant(f) and isPermutation(g))

    if mh:
        ulc = uhc
        slc = shc
    hom = (f.hom and isConstant(g)) or (isConstant(f) and g.hom) or (not isCommon(f,g) and isPermutation(f) and isPermutation(g)) or mh

    return Node('temp'+str(cnt), 'bvsubtract_op', f.width, ul, uh, sl, sh, ulc, uhc, slc, shc, hom, mh, vars)

def bvmultiply_tok(var1, var2, cnt):
    f = getNode(var1)
    g = getNode(var2)
    if (f.width != g.width):
        raise Exception('Width must match')
    
    umax = pow(2, f.width) - 1
    umin = 0
    smax = pow(2, f.width-1) - 1
    smin = -smax - 1
    tc = pow(2, f.width)

    vars = list(f.vars) + list(set(g.vars) - set(f.vars))
    if isConstant(f) and isConstant(g):
        ul = uh = f.ul * g.ul
        sl = sh = f.sl * g.sl
        ulc = uhc = slc = shc = 1
    else:
        if f.uh * g.uh > umax:
            ul = umin
            uh = umax
            ulc = umin + 1
            uhc = umax + 1
        else:
            ul = f.ul * g.ul
            uh = f.uh * g.uh
            if isCommon(f, g) or (isConstant(f) and f.ul == 0) or (isConstant(g) and g.ul == 0):
                ulc = 1
            else:
                ulc = max(f.ulc, g.ulc)
            uhc = min(f.uhc * g.uhc, tc)

        if f.sl * g.sl > smax or f.sh * g.sh > smax or f.sl * g.sh < smin or f.sh * g.sl < smin:
            sl = smin
            sh = smax
            slc = smin + 1
            shc = smax + 1
        else:
            sl = min(f.sl*g.sl, f.sh*g.sh, f.sl*g.sh, f.sh*g.sl)
            sh = max(f.sl*g.sl, f.sh*g.sh, f.sl*g.sh, f.sh*g.sl)
            if isCommon(f, g) or (isConstant(f) and f.sl == 0) or (isConstant(g) and g.sl == 0):
                slc = 1
            else:
                slc = max(f.slc, g.slc)
            shc = min(f.shc * g.shc, tc)

    hom = (f.hom and isConstant(g)) or (g.hom and isConstant(f))
    mh = f.mh and isConstant(g) and isPowerOfTwo(g.ul)

    hom = f.hom and isConstant(g) and isOddU(g)

    return Node('temp'+str(cnt), 'bvmultiply_op', f.width, ul, uh, sl, sh, ulc, uhc, slc, shc, hom, mh, vars)

def bvsdiv_tok(var1, var2, cnt):
    f = getNode(var1)
    g = getNode(var2)
    if (f.width != g.width):
        raise Exception('Width must match')
    if isConstant(g) and g.sl == 0:
        raise Exception('Divide-by-zero might occur')
    global isUnsigned
    isUnsigned = False
     
    umax = pow(2, f.width) - 1
    umin = 0
    smax = pow(2, f.width-1) - 1
    smin = -smax - 1
    tc = pow(2, f.width)

    vars = list(f.vars) + list(set(g.vars) - set(f.vars))
    if isConstant(f) and isConstant(g):
        ul = uh = int(f.ul / g.ul)
        sl = sh = int(f.sl / g.sl)
        ulc = uhc = slc = shc = 1
    else:

        ul = int(f.ul / g.uh)
        uh = int(f.uh / g.ul)
        
        ulc = 1
        if isConstant(f) and f.ul == 0:
            uhc = 1
        else:
            uhc = min(f.uhc * g.uhc, uh - ul + 1, tc)

        sl = min(f.sl/g.sl, f.sh/g.sh, f.sl/g.sh, f.sh/g.sl)
        sh = max(f.sl/g.sl, f.sh/g.sh, f.sl/g.sh, f.sh/g.sl)
        
        slc = 1
        if isConstant(f) and f.sl == 0:
            shc = 1
        else:
            shc = min(f.shc * g.shc, sh - sl + 1, tc)

    hom = (f.hom and isConstant(g)) or (g.hom and isConstant(f))
    mh = f.mh and isConstant(g) and isPowerOfTwo(g.sl)

    hom = f.hom and isConstant(g) and isOddS(g)

    return Node('temp'+str(cnt), 'bvsdiv_op', f.width, ul, uh, sl, sh, ulc, uhc, slc, shc, hom, mh, vars)

def bvudiv_tok(var1, var2,  cnt):
    f = getNode(var1)
    g = getNode(var2)
    if (f.width != g.width):
        raise Exception('Width must match')
    if isConstant(g) and g.sl == 0:
        raise Exception('Divide-by-zero might occur')
    global isSigned
    isSigned = False
     
    umax = pow(2, f.width) - 1
    umin = 0
    smax = pow(2, f.width-1) - 1
    smin = -smax - 1
    tc = pow(2, f.width)

    vars = list(f.vars) + list(set(g.vars) - set(f.vars))
    if isConstant(f) and isConstant(g):
        ul = uh = int(f.ul / g.ul)
        sl = sh = int(f.sl / g.sl)
        ulc = uhc = slc = shc = 1
    else:

        ul = int(f.ul / g.uh)
        uh = int(f.uh / g.ul)
        
        ulc = 1
        if isConstant(f) and f.ul == 0:
            uhc = 1
        else:
            uhc = min(f.uhc * g.uhc, uh - ul + 1, tc)

        sl = min(f.sl/g.sl, f.sh/g.sh, f.sl/g.sh, f.sh/g.sl)
        sh = max(f.sl/g.sl, f.sh/g.sh, f.sl/g.sh, f.sh/g.sl)
        
        slc = 1
        if isConstant(f) and f.sl == 0:
            shc = 1
        else:
            shc = min(f.shc * g.shc, sh - sl + 1, tc)

    hom = (f.hom and isConstant(g)) or (g.hom and isConstant(f))
    mh = f.mh and isConstant(g) and isPowerOfTwo(g.ul)

    hom = f.hom and isConstant(g) and isOddU(g)

    return Node('temp'+str(cnt), 'bvudiv_op', f.width, ul, uh, sl, sh, ulc, uhc, slc, shc, hom, mh, vars)

def and_tok(var1, var2, cnt):
    f = getNode(var1)
    g = getNode(var2)
    if (f.width != g.width):
        raise Exception('Width must match')
    
    vars = list(f.vars) + list(set(g.vars) - set(f.vars))

    if isConstant(f) and isConstant(g):
        return Node('temp'+str(cnt), 'and_op', f.width, ul, uh, sl, sh, ulc, uhc, slc, shc, mh, mh, vars)
    
    uh = min(f.uh, g.uh)
    ul = 0
    max_newrange = pow(2, maxNumOfBitsSetU(g))
    min_newrange = pow(2, minNumOfBitsSetU(g))
    max_d = pow(2, f.width) / min_newrange

    if isConstant(g):
        uhc = min(f.uhc, max_newrange)
    else:
        uhc = min(f.uhc * g.uhc, pow(2, f.width))

    if not isCommon(f, g) and max_d < f.ulc:
        ulc = int(f.ulc / max_d)
    else:
        ulc = 1

    mh = (f.mh and isConstant(g)) or (g.mh and isConstant(f))

    ### Signed abstracion not implemented yet
    sl = -pow(2, f.width - 1)
    sh = pow(2, f.width - 1) - 1
    slc = ulc
    shc = uhc
    ###

    return Node('temp'+str(cnt), 'and_op', f.width, ul, uh, sl, sh, ulc, uhc, slc, shc, mh, mh, vars)

def or_tok(var1, var2, cnt):
    f = getNode(var1)
    g = getNode(var2)
    if (f.width != g.width):
        raise Exception('Width must match')
    
    vars = list(f.vars) + list(set(g.vars) - set(f.vars))
    
    uh = max_or(f.uh, g.uh)
    ul = max(f.ul, g.ul)
    ldiv = pow(2, minNumOfBitsSetU(g))
    hdiv = pow(2, maxNumOfBitsSetU(g))
    hnr = pow(2, f.width) / ldiv
    lnr = pow(2, f.width) / hdiv

    if isConstant(g):
        uhc = min(f.uhc, hnr)
    else:
        uhc = min(f.uhc * g.uhc, pow(2, f.width))

    if isCommon(f, g) or hdiv > f.ulc:
        ulc = 1
    else:
        ulc = int(f.ulc / hdiv)

    mh = (f.mh and isConstant(g)) or (g.mh and isConstant(f))

    ### Signed abstracion not implemented yet
    sl = -pow(2, f.width - 1)
    sh = pow(2, f.width - 1) - 1
    slc = ulc
    shc = uhc
    ###

    return Node('temp'+str(cnt), 'or_op', f.width, ul, uh, sl, sh, ulc, uhc, slc, shc, mh, mh, vars)

def bvand_tok(var1, var2, cnt):
    f = getNode(var1)
    g = getNode(var2)
    if (f.width != g.width):
        raise Exception('Width must match')
    
    vars = list(f.vars) + list(set(g.vars) - set(f.vars))

    if isConstant(f) and isConstant(g):
        return Node('temp'+str(cnt), 'bvand_op', f.width, ul, uh, sl, sh, ulc, uhc, slc, shc, mh, mh, vars)
    
    uh = min(f.uh, g.uh)
    ul = 0
    max_newrange = pow(2, maxNumOfBitsSetU(g))
    min_newrange = pow(2, minNumOfBitsSetU(g))
    max_d = pow(2, f.width) / min_newrange

    if isConstant(g):
        uhc = min(f.uhc, max_newrange)
    else:
        uhc = min(f.uhc * g.uhc, pow(2, f.width))

    if not isCommon(f, g) and max_d < f.ulc:
        ulc = int(f.ulc / max_d)
    else:
        ulc = 1

    mh = (f.mh and isConstant(g)) or (g.mh and isConstant(f))

    ### Signed abstracion not implemented yet
    sl = -pow(2, f.width - 1)
    sh = pow(2, f.width - 1) - 1
    slc = ulc
    shc = uhc
    ###

    return Node('temp'+str(cnt), 'bvand_op', f.width, ul, uh, sl, sh, ulc, uhc, slc, shc, mh, mh, vars)

def bvor_tok(var1, var2, cnt):
    f = getNode(var1)
    g = getNode(var2)
    if (f.width != g.width):
        raise Exception('Width must match')
    
    vars = list(f.vars) + list(set(g.vars) - set(f.vars))
    
    uh = max_or(f.uh, g.uh)
    ul = max(f.ul, g.ul)
    ldiv = pow(2, minNumOfBitsSetU(g))
    hdiv = pow(2, maxNumOfBitsSetU(g))
    hnr = pow(2, f.width) / ldiv
    lnr = pow(2, f.width) / hdiv

    if isConstant(g):
        uhc = min(f.uhc, hnr)
    else:
        uhc = min(f.uhc * g.uhc, pow(2, f.width))

    if isCommon(f, g) or hdiv > f.ulc:
        ulc = 1
    else:
        ulc = int(f.ulc / hdiv)

    mh = (f.mh and isConstant(g)) or (g.mh and isConstant(f))

    ### Signed abstracion not implemented yet
    sl = -pow(2, f.width - 1)
    sh = pow(2, f.width - 1) - 1
    slc = ulc
    shc = uhc
    ###

    return Node('temp'+str(cnt), 'bvor_op', f.width, ul, uh, sl, sh, ulc, uhc, slc, shc, mh, mh, vars)

def bvxor_tok(var1, var2, cnt):
    f = getNode(var1)
    g = getNode(var2)
    #if (f.width != g.width):
    #    raise Exception('Width must match')
    
    vars = list(f.vars) + list(set(g.vars) - set(f.vars))
    
    if isConstant(g):
        ul = min_xorU(f, g.ul)
        uh = max_or(f.uh, g.uh)

        ### Signed abstracion not implemented yet
        sl = -pow(2, width - 1)
        sh = pow(2, width - 1) - 1
 
        return Node('temp'+str(cnt), 'bvxor_op', f.width, ul, uh, sl, sh, f.ulc, f.uhc, f.slc, f.shc, f.hom, f.mh, vars)

    if not isCommon(f, g):
        ulc = max(f.ulc, g.ulc)
    else:
        ulc = 1

    uhc = min(f.uhc * g.uhc, pow(2, f.width))
    hom = (not isCommon(f, g)) and ((g.mh and (isPermutation(f) or isConstant(f))) or (isPermutation(g) and (f.mh and isConstant(f))))
    
    ### Signed abstracion not implemented yet
    sl = -pow(2, f.width - 1)
    sh = pow(2, f.width - 1) - 1
    slc = ulc
    shc = uhc
    ###
 
    return Node('temp'+str(cnt), 'bvxor_op', f.width, 0, pow(2, f.width)-1, sl, sh, ulc, uhc, slc, shc, hom, False, vars)

def bvshiftl_tok(var1, var2, cnt):
    f = getNode(var1)
    g = getNode(var2)
    if (f.width != g.width):
        raise Exception('Width must match')
    
    vars = list(f.vars) + list(set(g.vars) - set(f.vars))
    
    if not isConstant(g):
        umax = pow(2, f.width)
        smax = pow(2, f.width-1)
        return Node('temp'+str(cnt), 'bvshiftl_op', f.width, 0, umax-1, -(smax), smax-1, 1, umax, 1, umax, False, False, vars)
    if g.ul >= f.width:
        return Node('temp'+str(cnt), 'bvshiftl_op', f.width, 0, 0, 0, 0, 1, 1, 1, 1, True, True, vars)
    uh = f.uh << g.ul
    if f.uh * pow(2, g.ul) > pow(2, f.width - 1):
        ul = 0
        hom = False
    else:
        ul = f.ul << g.ul
        hom = f.hom
    mh = f.mh and hom
    if g.ul < f.width and f.ulc > g.ul:
        nr = pow(2, f.width - g.ul)
        ulc = int(f.ulc / pow(2, g.ul))
    else:
        nr = 1
        ulc = 1
    uhc = min(f.uhc, nr)

    ### Signed abstracion not implemented yet
    sl = -pow(2, f.width - 1)
    sh = pow(2, f.width - 1) - 1
    slc = ulc
    shc = uhc
    ###
 
    return Node('temp'+str(cnt), 'bvshiftl_op', f.width, ul, uh, sl, sh, ulc, uhc, slc, shc, hom, mh, vars)

def bvshiftr_tok(var1, var2, cnt):
    f = getNode(var1)
    g = getNode(var2)
    #if (f.width != g.width):
    #    raise Exception('Width must match')
    
    vars = list(f.vars) + list(set(g.vars) - set(f.vars))
    
    if not isConstant(g):
        umax = pow(2, f.width)
        smax = pow(2, f.width-1)
        return Node('temp'+str(cnt), 'bvshiftr_op', f.width, 0, umax-1, -(smax), smax-1, 1, umax, 1, umax, False, False, vars)
    if pow(2, g.ul) > f.uh:   
        return Node('temp'+str(cnt), 'bvshiftr_op', f.width, 0, 0, 0, 0, 1, 1, 1, 1, True, True, vars)
    uh = f.uh >> g.ul
    ul = f.ul >> g.ul
    hom = f.mh & (pow(2, g.ul) <= f.ul)
    mh = hom
    
    if g.ul < f.width and f.ulc > g.ul:
        nr = pow(2, f.width - g.ul)
        ulc = int(f.ulc / pow(2, g.ul))
    else:
        nr = 1
        ulc = 1
    uhc = min(f.uhc, nr)
    
    ### Signed abstracion not implemented yet
    sl = -pow(2, f.width - 1)
    sh = pow(2, f.width - 1) - 1
    slc = ulc
    shc = uhc
    ###
 
    return Node('temp'+str(cnt), 'bvshiftr_op', f.width, ul, uh, sl, sh, ulc, uhc, slc, shc, hom, mh, vars)

def concat_tok(var1, var2, cnt):

    f = getNode(var1)
    g = getNode(var2)
    
    vars = list(f.vars) + list(set(g.vars) - set(f.vars))
    width = f.width + g.width
    uh = f.uh * pow(2, g.width) + g.uh
    ul = f.ul * pow(2, g.width) + g.ul
    sh = f.sh * pow(2, g.width) + g.sh
    sl = f.sl * pow(2, g.width) + g.sl
    ulc = f.ulc * g.ulc
    uhc = f.uhc * g.uhc
    mh = (f.mh and isConstant(g)) or (g.mh and isConstant(f))
    
    ### Signed abstracion not implemented yet
    slc = ulc
    shc = uhc
    ###
 
    return Node('temp'+str(cnt), 'bvconcat_op', width, ul, uh, sl, sh, ulc, uhc, slc, shc, mh, mh, vars)

def extract_tok(parse, cnt):
    f = getNode(parse[3])
    low_index = int(parse[2])
    hi_index = int(parse[1])

    width = hi_index - low_index + 1
    
    if f.uh > pow(2, hi_index):
        uh = pow(2, width) - 1
    elif f.uh < pow(2, low_index):
        uh = 0
    else:
        uh = f.uh >> low_index

    if f.ul < pow(2, low_index):
        ul = f.ul
    elif f.ul > pow(2, high_index):
        ul = 0
    else:
        ul = f.ul >> low_index

    max_d = pow(2, f.width - width)

    uhc = min(f.uhc, pow(2, width))
    if max_d > f.ulc :
        ulc = 1
    else:
        ulc = int(f.ulc / max_d)

    ### Signed abstracion not implemented yet
    sl = -pow(2, width - 1)
    sh = pow(2, width - 1) - 1
    slc = ulc
    shc = uhc
    ###
    
    return Node('temp'+str(cnt), 'bvextract_op', width, ul, uh, sl, sh, ulc, uhc, slc, shc, f.mh, f.mh, f.vars)

def sign_extend_tok(parse, cnt):
    
    f = getNode(parse[2])
    
    width = int(parse[1]) + f.width
    
    return Node('temp'+str(cnt), 'bvsign_extend_op', width, f.ul, f.uh, f.sl, f.sh, f.ulc, f.uhc, f.slc, f.shc, f.hom, f.mh, f.vars)

def summary(parse):
    global temps, tmp_cnt
    print (parse)
    parse_vars = parse[1:]
    num_vars = len(parse_vars)
    if parse[0] == '=':
        node = eq_tok(parse[1], parse[2], tmp_cnt)
    elif parse[0] == 'not':
        if getNode(parse[1]).type == 'bveq_op':
            node = noteq_tok(parse)
    elif parse[0] == 'bvult':
        node = bvult_tok(parse[1], parse[2], tmp_cnt)
    elif parse[0] == 'bvugt':
        node = bvugt_tok(parse[1], parse[2], tmp_cnt)
    elif parse[0] == 'bvslt':
        node = bvslt_tok(parse[1], parse[2], tmp_cnt)
    elif parse[0] == 'bvsgt':
        node = bvsgt_tok(parse[1], parse[2], tmp_cnt)
    elif parse[0] == 'bvsle':
        node = bvsle_tok(parse[1], parse[2], tmp_cnt)
    elif parse[0] == 'bvsge':
        node = bvsge_tok(parse[1], parse[2], tmp_cnt)
    elif parse[0] == 'and':
        for i in range(num_vars-1):
            node = and_tok(parse[i+1], parse[i+2], tmp_cnt)
            temps.append(node)
            if i != num_vars-2:
                tmp_cnt += 1
            parse[i+2] = node.name

    elif parse[0] == 'or':
        for i in range(num_vars-1):
            node = or_tok(parse[i+1], parse[i+2], tmp_cnt)
            temps.append(node)
            if i != num_vars-2:
                tmp_cnt += 1
            parse[i+2] = node.name
    elif parse[0] == 'bvadd':
        for i in range(num_vars-1):
            node = bvadd_tok(parse[i+1], parse[i+2], tmp_cnt)
            temps.append(node)
            if i != num_vars-2:
                tmp_cnt += 1
            parse[i+2] = node.name
    elif parse[0] == 'bvsub':
        node = bvsubtract_tok(parse[1], parse[2], tmp_cnt)
    elif parse[0] == 'bvmul':
        for i in range(num_vars-1):
            node = bvmultiply_tok(parse[i+1], parse[i+2], tmp_cnt)
            temps.append(node)
            if i != num_vars-2:
                tmp_cnt += 1
            parse[i+2] = node.name
    elif parse[0] == 'bvsdiv':
        node = bvsdiv_tok(parse[1], parse[2], tmp_cnt)
    elif parse[0] == 'bvudiv':
        node = bvudiv_tok(parse[1], parse[2], tmp_cnt)
    elif parse[0] == 'bvand':
        for i in range(num_vars-1):
            node = bvand_tok(parse[i+1], parse[i+2], tmp_cnt)
            temps.append(node)
            if i != num_vars-2:
                tmp_cnt += 1
            parse[i+2] = node.name
    elif parse[0] == 'bvor':
        for i in range(num_vars-1):
            node = bvor_tok(parse[i+1], parse[i+2], tmp_cnt)
            temps.append(node)
            if i != num_vars-2:
                tmp_cnt += 1
            parse[i+2] = node.name
    elif parse[0] == 'bvxor':
        for i in range(num_vars-1):
            node = bvxor_tok(parse[i+1], parse[i+2], tmp_cnt)
            temps.append(node)
            if i != num_vars-2:
                tmp_cnt += 1
            parse[i+2] = node.name
    elif parse[0] == 'bvshl':
        node = bvshiftl_tok(parse[1], parse[2], tmp_cnt)
    elif parse[0] == 'bvlshr':
        node = bvshiftr_tok(parse[1], parse[2], tmp_cnt)
    elif parse[0] == 'concat':
        node = concat_tok(parse[1], parse[2], tmp_cnt)
    elif parse[0] == 'extract':
        node = extract_tok(parse, tmp_cnt)
    elif parse[0] == 'sign_extend':
        node = sign_extend_tok(parse, tmp_cnt)
    elif parse[0] == '_':
        if re.search(r'bv([0-9]+)', parse[1]):
            match = re.search(r'bv([0-9]+)', parse[1])
            num = int(match.group(1))
            node = Node('temp'+str(tmp_cnt), 'bvconst', int(parse[2]), num, num, num, num, 1, 1, 1, 1, True, True, [])
        else:
            node = 2
    elif parse[0] == 'assert':
        node = 1
    else:
        raise Exception('Cannot parse ' + parse[0])
    if not isinstance(node, int):
        node.printNode()
    return node 

def parenthetic_contents(string):
    """Generate parenthesized contents in string as pairs (level, contents)."""
    stack = []
    global nodes, temps, tmp_cnt
    cnt = 0
    while True:
        for i, c in enumerate(string):
            if c == '(':
                stack.append(i)
            elif c == ')' and stack:
                start = stack.pop()
                #yield (len(stack), string[start + 1: i])
                if (len(stack) != 0):
                    parse = string[start + 1: i].split()
                    #print(string, parse, len(stack))

                    temp_node = summary(parse)
                    print(string)
                    if temp_node == 1:
                        break
                    elif temp_node == 2:
                        string = string.replace(string[start : i + 1],string[start + 3 : i])
                        break
                    else:    
                        temps.append(temp_node)
                        string = string.replace(string[start : i + 1],"temp"+str(tmp_cnt)+" ")
                        tmp_cnt += 1
                        break
                else:
                    break
        
        if stack:
            while stack:
                stack.pop()
        else:
            break
    
    return temps[-1]

def main():
    #proj_vars = re.split(' ', sys.argv[1])
    file = open(sys.argv[1], "r")
    line = file.readline()
    lines = []
    global nodes
    lines.append(line)
    """ Parsing variables """
    while line:
        if (line.find('declare-fun') != -1):
            node_desc = re.split(' |\(|\)', line)
            width = int(node_desc[9])
            umax = pow(2, width)
            smax = pow(2, width-1)
            nodes.append(Node(node_desc[2], node_desc[8], width, 0, umax-1, -(smax), smax-1, umax, umax, umax, umax, True, True, [node_desc[2]]))
            #nodes[node_desc[2]] = {'type': node_desc[8], 'width': width, 'ul': 0, 'uh': umax-1, 'sl': -(smax), 'sh': smax-1, 'ulc': umax, 'uhc': umax,'slc': umax, 'shc': umax, 'hom': True, 'hm': True, 'vars': [] }
        line = file.readline()
        lines.append(line)
 
    """ Assertions """
    for line in lines:
        if (line.find('assert') != -1):
            contents = parenthetic_contents(line)
            #for content in contents:
            #    print(content)
    for node in nodes:
        node.printNode()

nodes = []
temps = []
tmp_cnt = 0
bounds = []
isSigned = True
isUnsigned = True
main()
if not isSigned:
    print('Signed representation might be wrong')
if not isUnsigned:
    print('Unsigned representation might be wrong')

for bound in bounds:
    print(bound.ula, bound.uha, bound.sla, bound.sha, bound.vars)

for i in range(len(bounds)-1):
    bound = mergeBounds(bounds[i], bounds[i+1])
    bounds[i+1] = bound
bounds[-1].printBound()
