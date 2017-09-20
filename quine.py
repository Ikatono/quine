from math import ceil
from math import log

def quine(truth, dontcare=None, bits=0):
    if dontcare is None:
        dontcare = []
    
    if bits == 0:
        bits = int(ceil(log(max(truth + dontcare),2)))
    
    d = [None] * bits
    
    getterms = truth + dontcare
    
    #collect all terms
    nextcol = [[] for i in range(bits+1)]
    for item in getterms:
        tmp = item
        tru = ['0'] * bits
        for i in range(bits-1, -1, -1):
            if tmp >= 2**i:
                tmp -= 2**i
                tru[i] = '1'
        asterm = term(tru)
        nextcol[asterm.group] += [asterm]
    
    d[0] = nextcol
    
    #print(d)
    #return d
    
    for col in range(bits-1):
        nextcol = [[] for i in range(bits-col+1)]
        for group in range(bits-col):
            for item1 in d[col][group]:
                for item2 in d[col][group+1]:
                    if item1.match(item2):
                        asterm = item1.merge(item2)
                        item1.prime = False
                        item2.prime = False
                        if asterm not in nextcol[group]:
                            nextcol[group] += [asterm]
        
        d[col+1] = nextcol
    return d
    
    pimp = term.allprime(d)
    #return pimp
    defdict = {}
    for i in truth:
        defdict[i] = False
    ptable = [None] * len(pimp)
    #return ptable
    for i in range(len(pimp)):
        ptable[i] = defdict.copy()
        for min in truth:
            ptable[i][min] = min in pimp[i].mins
    #return ptable
    prevess = []
    ess = []
    covered = set([])
    while True:
        for min in [x for x in truth if x not in covered]:
            terms = []
            for i in range(len(ptable)):
                if ptable[i][min]:
                    terms += [i]
            #print(terms)
            if len(terms) == 1:
                #print('test')
                ess += [pimp[terms[0]]]
                #print(ess)
                del ptable[terms[0]]
                del pimp[terms[0]]
                #print(ess)
                # for i in ptable:
                    # del i[min]
                #print(ess)
                covered.add(min)
        break
        if ess == prevess:
            break
        prevess = ess
    
    notcovered = [x for x in truth if x not in covered]
    
    #for 
    
    return pimp, ess, ptable, covered, notcovered

def tovhdl(terms):
    asstr = ''
    for i in range(len(terms)):
        asstr += 'T(%d) <= ' % i
        strt = 0
        while True:
            if terms[i].truth[strt] == '1':
                asstr += chr(65+strt) + ' '
                break
            elif terms[i].truth[strt] == '0':
                asstr += 'not ' + chr(65+strt) + ' '
                break
            strt += 1
                
        for j in range(strt+1,len(terms[i].truth)):
            if terms[i].truth[j] == 'x':
                continue
            asstr += ' and '
            if terms[i].truth[j] == '0':
                asstr += 'not '
            asstr += chr(j+65)
        asstr += ';\n'
    return asstr
        
    
def getexpansion(terms):
    asstr = []
    for term in terms:
        m = ''
        for i in range(len(term.truth)):
            if term.truth[i] == 'x':
                continue
            m += chr(65+i)
            if term.truth[i] == '0':
                m += "'"
        asstr.append(m)
    fstring = ''
    for i in range(len(terms)-1):
        fstring += asstr[i] + ' + '
    fstring += asstr[-1]
    return fstring
        
def petterms():
    pass

class term:
    
    def __init__(self, truth):
        self.truth = truth
        self.group = sum([1 if i == '1' else 0 for i in self.truth])
        
        dc = []
        num = 0
        for i in range(len(self.truth)):
            if self.truth[i] == '1':
                num += 2**i
            elif self.truth[i] == 'x':
                dc += [2**i]
        vals = [num]
        for term in dc:
            vals += [val + term for val in vals]
        self.mins = vals
        
        self.prime = True
        
    
    def __eq__(self, other):
        return self.truth == other.truth
    
    def match(self, other):
        if len(self.truth) != len(other.truth):
            raise ValueError('truth values must have equal length')
        
        cnt = 0
        for i in range(len(self.truth)):
            if self.truth[i] == 'x' and other.truth[i] == 'x':
                continue
            elif self.truth[i] == 'x' or other.truth[i] == 'x':
                return False
            elif self.truth[i] != other.truth[i]:
                cnt += 1
        return cnt == 1
    
    #never use without verifying terms match first
    def merge(self, other):
        if len(self.truth) != len(other.truth):
            raise ValueError('truth values must have equal length')
        
        newtruth = ['0'] * len(self.truth)
        for i in range(len(self.truth)):
            if self.truth[i] == other.truth[i] != 'x':
                newtruth[i] = self.truth[i]
            else:
                newtruth[i] = 'x'
        return term(newtruth)
    
    @staticmethod
    def allterms(lst):
        if isinstance(lst, term):
            return set(lst.mins)
        else:
            mins = set()
            for i in lst:
                mins.update(set(term.allterms(i)))
            return mins
    
    @staticmethod
    def allprime(lst):
        if isinstance(lst, term):
            return [lst] if lst.prime else []
        else:
            terms = []
            for item in lst:
                terms += term.allprime(item)
            return terms