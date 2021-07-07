
"""Minimization of multivalued logical expressions

quine mcclusky algorithm for minimizing boolean expressions is generalized here 
to minimize multivalued expression
as example 'a>=1 and b>=2 or a==1 and b>=3 and c<=1'
for a multivalued expression we need to specify the range of values for each variable
here these are all integers between 0 and a max value specified in a max_val_dict 
e.g. {'a':2,'b':3,'c':3}

USAGE EXAMPLIFIED:

>>>import logicfun as lf
>>>muex='a>=1 and b>=2 or a==1 and b>=3 and c<=1'
>>>max_val_dict={'a':2,'b':3,'c':3}
>>>lf.minexpr(muex,max_val_dict)
'a>=1 and b>=2'

>>>mm='a>=1 and c>=1 or b>=2 and not c>=2 or not a>=3 or not b>=3'
>>>lf.minexpr(mm,compdict)
'True'



5 vars: ttbl:
[0,1,2,3,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,27,28,29,30,31]

exps='not a>=1 and not b>=1 and not c>=1 and not d>=1 or a>=1 and not b>=1 and not c>=1 and not d>=1 or not a>=1 and not b>=1 and c>=1 and not d>=1 or a>=1 and not b>=1 and c>=1 and not d>=1 or not a>=1 and not b>=1 and not c>=1 and d>=1 or a>=1 and not b>=1 and not c>=1 and d>=1 or a>=1 and b>=1 and not c>=1 and d>=1 or a>=1 and b>=1 and c>=1 and d>=1'

"""

import re
import random
import time
import string



class Logicfun:

    def __init__(self,comps,Max):

        self.comps=comps # names of variables
        self.Max=Max # max values of variables (min value is zero)
        self.N=sum(Max) 

        self.cmpltt=[]  #complete truth table (all assignments return True)
        self.levprod=[1]
        self.nlevs=[]
        self.chivars=['nn' for c in Max] # 01-vectors (bin-numbers) that give for each multi var the place of Boolean vars
        for i,c in enumerate(Max):
            self.chivars[i]=(2**c-1)<<sum(Max[:i])
            self.levprod.append(self.levprod[-1]*(c+1))
            self.nlevs.append(c+1)
        for i in range(self.levprod[-1]):
            state=[]
            for k in range(len(Max)):
                state.append((i//self.levprod[k])%self.nlevs[k])

            bstate=0
            for i,s in enumerate(state):
                for j in range(s):
                    bstate += 1<<(sum(Max[:i])+j)
            self.cmpltt.append(bstate)

    def bits(self,number):
        """
        helper to counts bits in a number
        """
        count=0
        for i in range(self.N):
            count+=number>>i&1
        return count

    def minimise(self,ttbl,multi=True):
        """
        minimise given truth table
        multi: indicating if dealing with multivalued logic expression
        """
        if multi: getprimes_fun = self.getprimesmulti
        else : getprimes_fun = self.getprimestdrt
        ttbl=list(ttbl)
        if len(ttbl)==0:
            return 0
        elif set(ttbl)==set(self.cmpltt):
            return 1
        else:
            primes=getprimes_fun(ttbl)
            cols,_,_=self.reducing(primes,ttbl)
            primecov=self.advprimecover(cols,primes)
            return primecov

    def getprimestdrt(self,ttbl):
        """
        boolean standard algo to get primes implicants
        """
        newterms=[set([]) for i in range(self.N+1)]
        for i,t in enumerate(ttbl):
            newterms[self.bits(t)].add((t,t))
        eatenB=set([])
        primes=[]
        while newterms:
            minterms=[c.copy() for c in newterms]+[set([])]
            newterms=[]
            for i in range(len(minterms)-1):
                new=set([])
                eatenA=eatenB.copy()
                eatenB=set([])

                for a in minterms[i]:
                    for b in minterms[i+1]:
                        if a[0]^a[1]==b[0]^b[1] and self.bits((a[1]^b[0])&b[0])==1:
                            new.add((a[0]&b[0],a[1]|b[1]))
                            eatenA.add(a)
                            eatenB.add(b)

                #print len(minterms[i]),len(eatenA)
                primes+=[p for p in minterms[i]-eatenA]
                #print len(primes),'primes'
                #print len(new),'new'
                if new:
                    newterms.append(new)
        return primes

    def getprimesmulti(self,ttbl):
        """
		this function gives the iteration of multi-merge to obtain the
		prime implicants according to the ordering that adheres to the
		multivalued logic. The multi-merge rule is given as a second if test
		results in a merge.

		The representation of implicants is given by  two variables, which are
		boolean vectors. The first boolean vector is True at those Boolean variables,
		where the implicant is true only. The second vector is True,
		at the True variables and at the don't care variables.
        """

        newterms=[set([]) for i in range(self.N+1)]  # the implicants that
		#are tested and merged in the next iteration that are obtained by merging
        for i,t in enumerate(ttbl):  # in the beginning the true points are the implicants
            newterms[self.bits(t)].add((t,t))  # no don't cares (DC), so (t,t)
        eatenB=set([])  # those that were merged are 'eaten', they will be discarded
        primes=[] #initilaise list for prime implicants
        while newterms:
            minterms=[c.copy() for c in newterms]+[set([])] # copy the implicants for this iteration
            newterms=[]
            for i in range(len(minterms)-1):
                new=set([])
                eatenA=eatenB.copy()
                eatenB=set([])

                for a in minterms[i]:
                    for b in minterms[i+1]:
                        if a[0]^a[1]==b[0]^b[1] and self.bits((a[1]^b[0])&b[0])==1:
                            new.add((a[0]&b[0],a[1]|b[1]))
                            eatenA.add(a)
                            eatenB.add(b)
                        else:    # additional possibility to merge minterms because of multivalue-implications between variables
                            for vslice in self.chivars: #for each multi var, vslice will serve as mask to read except one Boolean vars of one multi var
                                # if only in one vslice (only one multivar) there is difference and only with one of a,b dont care then merge
                                if a[0]|vslice==b[0]|vslice and a[1]|vslice==b[1]|vslice and a[0]&b[1]==a[0] and a[1]&b[0]==b[0]:
                                    new.add((a[0]&b[0],a[1]|b[1]))
                                    eatenA.add(a)
                                    eatenB.add(b)
                primes+=[p for p in minterms[i]-eatenA]
                if new:
                    newterms.append(new)
        return primes

    def reducing(self,primes,ttbl):
        """
    	the list of all primes has to be reduced to a minimal prime cover, which is
    	a classic combinatorial problem (set covering), first step is to known column
    	and row reduction.
    	"""
        def colreduce(rows,cols,dltcols):
            deletion=False
            for i,x in enumerate(cols):
                if x and i not in dltcols:
                    for j,y in enumerate(cols[i+1:]):
                        if y and j+i+1 not in dltcols:
                            if y<=x:
                                dltcols.add(i) #delete x
                                deletion=True
                                break
                            elif x<y:
                                dltcols.add(i+j+1) #delete y
                                deletion=True
            for r in rows:
                r-=dltcols
            return deletion

        def rowreduce(rows,cols,dltrows):
            deletion=False
            for i,x in enumerate(rows):
                if x and i not in dltrows:
                    for j,y in enumerate(rows[i+1:]):
                        if y and j+i+1 not in dltrows:
                            if x<=y:
                                dltrows.add(i) #delete x
                                deletion=True
                                break
                            elif y<x:
                                dltrows.add(i+j+1) #delete y
                                deletion=True
            for c in cols:
                c-=dltrows
            return deletion


        M=len(ttbl)
        cols=[set([]) for c in range(M)]
        rows=[set([]) for c in range(len(primes))]
        for i,m in enumerate(ttbl):
            for j,p in enumerate(primes):
                if p[0]&m==p[0] and p[1]&m==m:
                    rows[j].add(i)
                    cols[i].add(j)

        dltcols=set([])
        dltrows=set([])
        while colreduce(rows,cols,dltcols):
            if not rowreduce(rows,cols,dltrows):
                break
        for i in dltcols:
            cols[i]=0

        return cols,len(dltcols),len(dltrows)



    def advprimecover(self,cols,primes):
        """
    	find minimal prime cover 
        improved algo with divide and conquer approach to reduce run-time
    	"""
        def halfprimecover(columns,primes):
            game=set([0])
            columns.sort(key=lambda x:len(x))
            for column in columns:
                if column:
                    nxgame=set([])
                    for s in game:
                        new=set([])
                        for x in column:
                            if s|x==s:
                                new=set([s])
                                break
                            else:
                                for y in nxgame:
                                    if (s|x)&y==y:
                                        break
                                else:
                                    new.add(s|x)
                        nxgame|=new
                    
                    game=sorted(list(nxgame),key=lambda x: self.bits(x),reverse=True)
            endgame=sorted(list(game),key=lambda x: (self.bits(x),x))
            return endgame

        if len(primes)<=15:
            return self.primecover(cols,primes)
        columns=[[] for c in cols]
        for i,c in enumerate(cols):
            if c:
                for t in c:
                    columns[i].append(1<<t)
        m=len(columns)
        cols1=columns[:m//2]
        cols2=columns[m//2:]
        game1=halfprimecover(cols1,primes)
        game2=halfprimecover(cols2,primes)


        pairs=[(a,b) for a in game1 for b in game2]
        #pairs.sort(key=lambda x: max(self.bits(a),self.bits(b)))

        opt=float('inf')
        for a,b in pairs:
            if max(self.bits(a),self.bits(b))>=opt:
                break
            x=a|b
            size=self.bits(x)
            if size<opt:
                sol=x
                opt=size

        prsol=[]
        for i,p in enumerate(primes):
            if sol>>i&1:
                prsol.append(p[:2])
        return prsol


    def primecover(self,cols,primes):
        columns=[[] for c in cols]
        game=set([0])
        sol=0
        for i,c in enumerate(cols):
            if c:
                for t in c:
                    columns[i].append(1<<t)
        columns.sort(key=lambda x:len(x))
        for column in columns:
            if column:
                nxgame=set([])
                for s in game:
                    new=set([])
                    for x in column:
                        if s|x==s:
                            new=set([s])
                            break
                        else:
                            for y in nxgame:
                                if (s|x)&y==y:
                                    break
                            else:
                                new.add(s|x)
                    nxgame|=new
                
                game=sorted(list(nxgame),key=lambda x: self.bits(x),reverse=True)
        endgame=sorted(list(game),key=lambda x: (self.bits(x),x))
        sol=endgame[0]
        prsol=[]
        for i,p in enumerate(primes):
            if sol>>i&1:
                prsol.append(p[:2])
        return prsol


    def readexpr(self,expression):
        comps=self.comps[:]
        localMax=self.Max
        ttbl=[]
        wordlist=expression.split()
        for i,w in enumerate(wordlist):
            if re.search('[=<>]',w):
                for j,c in enumerate(comps):
                    w=re.sub(c+r'(?=[<>=+\s-])','state[%d]'%j,w)
                    w=re.sub(r'(?<=[<>=+\s-])'+c,'state[%d]'%j,w)
                wordlist[i]=w[:]
        expression=' '.join(wordlist)
        #GENERATE MULTIVALUE STATES
        levprod=[1]
        nlevs=[]
        for c in localMax:
            levprod.append(levprod[-1]*(c+1))
            nlevs.append(c+1)
        for i in range(levprod[-1]):
            state=[]
            for k in range(len(localMax)):
                state.append((i//levprod[k])%nlevs[k])

            if eval(expression):
                #transform multivalue state into state of representing boolean variables
                bstate=0
                for i,s in enumerate(state):
                    for j in range(s):
                        bstate += 1<<(sum(localMax[:i])+j)
                ttbl.append(bstate)

        return ttbl

    def writeexpr(self,primes, brackets=False):

        """ this extended version of writeexpression is meant to write the
        expressions most conveniently, i.e. using == as well , a>=2 and not a>=3
        is substituted by a==3
        for a>=2 and not a>=4 it would write  2<=a<=3
        """
        if primes==0:
            return 'False'
        elif primes==1:
            return 'True'
        else:
            comps=self.comps
            localMax=self.Max
            conj=[]
            for p in primes:
                lits=[]
                for i,comp in enumerate(comps):
                    cmprange=range(sum(localMax[:i]),sum(localMax[:i+1]))
                    poslit=[]
                    neglit=[]
                    #print len(cmprange)
                    for j,k in enumerate(cmprange):
                        if j==0:
                            #print 'if'
                            if p[0]>>k&1:
                                poslit=1
                            elif not p[1]>>k&1:
                                neglit=0
                                poslit=0
                                break
                        if j==len(cmprange)-1:
                            #print 'elif'
                            if p[0]>>k&1:
                                poslit=j+1
                                neglit=j+1
                                break
                            elif not p[1]>>k&1 and neglit==[]:
                                neglit=j
                        elif not j==0:
                            #print 'else'
                            if p[0]>>k&1:
                                poslit=j+1
                            elif not p[1]>>k&1 and neglit==[]:
                                neglit=j
                    #print poslit,neglit
                    if not poslit==[]:
                        if poslit==neglit:
                            lits.append(comp+'==%d'%poslit)
                        elif not neglit==[]:
                            lits.append('%d<='%poslit+comp+'<=%d'%neglit)
                        else:
                            lits.append(comp+'>=%d'%poslit)
                    elif not neglit==[]:
                        lits.append(comp+'<=%d'%neglit)
                if (not brackets) or (len(lits)<=1):
                    conj.append(' and '.join(filter(lambda x:x,lits)))
                else:
                    conj.append('('+' and '.join(filter(lambda x:x,lits))+')')
            expr=' or '.join(conj)
            return expr


    def readboolexpr(self,expression):
        expression=' '+expression.replace('(',' ( ').replace(')',' ) ')+' '
        comps=self.comps[:]
        comps.reverse()
        N=len(comps)
        # in expression replace variable names by states[j] list entry calls for evaluation later
        expr=' '+expression+' '
        state=[0 for i in comps]
        # produce list of indices of true-evaluation in the truth table of the expression:
        ttbl=[]
        #therefor generate all assignments (states) of variables and evaluate expression,
        #if evaluates true, add index of assignment to list
        for j,c in enumerate(comps):
            expr=expr.replace(' '+c+' ',' state[%d] '%j)
        for x in range(1<<N):
            for j in range(N):
                state[N-j-1]=(x>>j)&1
            if eval(expr):
                ttbl.append(x)
        return ttbl

    def writeboolexpr(self,primes,brackets=False):

        if primes==0: return 'False'
        elif primes==1: return 'True'
        else:
            comps=self.comps[:]
            #comps.reverse()
            conj=[]
            for p in primes:
                lits=[]
                for k,comp in enumerate(comps):
                    if p[0]>>k&1:
                        lits.append(comp)
                    elif not p[1]>>k&1:                       #or false
                        lits.append('not '+comp)
                if (not brackets) or (len(lits)<=1):
                    conj.append(' and '.join(lits))
                else:
                    conj.append(' ('+' and '.join(lits)+') ')

            expr=' or '.join(conj)
            return expr

def minexpr(expression, maxvals, brackets=False):  
    """
    calculated minimal form of multivalued logical expression

    expression: the multivalue expression to be minimized
    maxvals: dictionary of max values for each variable (min value is 0 and tange are all integers between)

    
    """                                    

    expression=' '+expression.replace('(',' ( ').replace(')',' ) ')+' '
    if type(maxvals)==int and maxvals==1:
        return minboolexpr(expression, brackets)
    elif type(maxvals)==int:
        comps=list(set(re.findall(r'([^=<>\s]+(?=[=><]))',expression)))
        compdict=dict(zip(comps,[maxvals for c in comps]))
        #print compdict
    elif type(maxvals)==dict:
        compdict=maxvals
    else:
        print( 'Wrong 2nd input, dictionary of components or single integer expected')
        return None
    comps = list(compdict.keys())
    maxvals = [compdict[x] for x in comps]
    lgfun=Logicfun(comps,maxvals)
    ttbl=lgfun.readexpr(expression)
    pc=lgfun.minimise(ttbl)
    minex=lgfun.writeexpr(pc,brackets)
    # verify equivalence before returning
    minttbl=lgfun.readexpr(minex)
    assert set(ttbl)==set(minttbl), "unknown failure - calculation yields incorrect result"
    return minex

def minboolexpr(expression,brackets=False):
    expression=' '+expression.replace('(',' ( ').replace(')',' ) ')+' '
    comps=sorted(list(set([c.replace('not','').strip('() ') for j in expression.split(' or ') for c in j.split(' and ')])))
    maxvals=[1 for c in comps]
    lgfun=Logicfun(comps,maxvals)
    ttbl=lgfun.readboolexpr(expression)
    pc=lgfun.minimise(ttbl)
    minex=lgfun.writeboolexpr(pc,brackets)
    # verify equivalence before returning
    minttbl=lgfun.readboolexpr(minex)
    assert set(ttbl)==set(minttbl), "unknown failure - calculation yields incorrect result"
    return minex

def guess_max_vals(expr):
    """
    assign value range to all variables in expression

    expr: string that defines multivalued logical expression
    returns dictionary of variables that could be parsed from 
    expression and max values for each variable
    max values are chosen such that each term could be true with given 
    value assignment, i.e. "A > 4" -> A has max value 5 , "A>=4" -> max value 4
    """
    terms = re.split('and not|or not|and|or|not', expr)
    vnames_values = [re.split('<=|==|>=|>|<', x) for x in terms if x.strip()!=""]
    vnames = [x[0].strip() for x in vnames_values]
    values = [x[1].strip() for x in vnames_values]
    operators = [re.search('<=|==|>=|>|<', x).group() for x in terms if x.strip()!=""]
    # increase max value for > operator
    values_ad = [int(x)+int(y==">") for x,y in zip(values,operators)]
    guess_max_dict = {}
    for n,v in zip(vnames, values_ad):
        guess_max_dict[n] = max(guess_max_dict.get(n,0), v)
    return guess_max_dict


def random_multi_expression(n_vars, max_val_dict=False, n_terms=False):
    """
    creates a random multivalue logical expression

    n_vars: number of variables to use 
    max_val_dict: dict of variables and max value for each (min value is 0)
    if max_val_dict is not passed it will be random sampled with max vals between 1 and 4
    n_terms: number of terms to sample (resulting expr can have less due to duplicates)
    returns the multivalue logical expression and the max_val_dict
    """

    comparisons = ["<", "==", "<=", ">=", ">"]
    logical_op = ["and", "or", "and not", "or not"]
    # weights on picking logical opertors, reduce OR to avoid expression equiv. to True
    op_weights = [3, 1, 2, 1]
    
    if max_val_dict:
        variables = list(max_val_dict.keys())
        assert(n_vars==len(variables))
    else:
        variables = list(string.ascii_uppercase)[:n_vars]
        max_val_dict = {v: random.randint(1,4) for v in variables}
    
    if not n_terms:
        n_terms = random.randint(5,30)
    # create each term 
    terms = []
    for k in range(n_terms):
        var = variables[random.randint(0,n_vars-1)]
        value = random.randint(0,max_val_dict[var])
        # for value min or max do not use < resp. > comparison
        # to avoid terms equivalent to False
        if value==0:
            comp = comparisons[random.randint(1,4)]
        elif value==max_val_dict[var]:
            comp = comparisons[random.randint(0,3)]
        else:    
            comp = comparisons[random.randint(0,4)]
        terms.append(''.join([var, comp, str(value)]))
    # deduplicate terms and connect with sampled logic operators
    terms = list(set(terms))
    logic_ops = random.choices(logical_op, weights=op_weights, k=len(terms)-1)+[""]
    expr = " ".join([x+" "+y for x, y in zip(terms,logic_ops)])
    return expr, max_val_dict


def testwrite(N,*args):
    """
    run a number N of test for correctness of read and write functions

    """
    lgfun=Logicfun(['x%d'%i for i in range(N)],[1 for i in range(N)])
    error=False
    if args:
        ttt=args[0]
        print( ttt)
    else:
        ttt=list(range(1<<N))
        random.shuffle(ttt)
    tz=time.time()
    for i in range(1<<(N-1),(1<<(N))-1):

        z=time.time()
        #print 'truthtable:',i#sorted(ttt[:i]),i
        pc=lgfun.minimise(ttt[:i])
        z=time.time()-z


        minex=lgfun.writeexpr(pc)
        rtt=lgfun.readexpr(minex)
        if not set(rtt)==set(ttt[:i]):
            error=True
            print('***************  ERROR  *************************')
            print( 'result=',rtt)

    if not error:
        print( ':::::::::::::: all correct :::::::::::::::')
    print( 'total time:',time.time()-tz)

    tz=time.time()


def test_minimise(N,*args):
    """
    run a number N of test for correctness of minimise function 

    this checks that input and output expression are equivalent
    """
    lgfun=Logicfun(['x%d'%i for i in range(N)],[1 for i in range(N)])
    error=False
    if args:
        ttt=args[0]
        print( ttt)
    else:
        ttt=list(range(1<<N))
        random.shuffle(ttt)
    tz=time.time()
    for i in range(1<<(N-1),(1<<(N))-1):

        z=time.time()
        #print 'truthtable:',i#sorted(ttt[:i]),i
        pc=lgfun.minimise(ttt[:i])
        z=time.time()-z
        rt=[]

        if pc:
            for m in range(1<<N):
                for p in pc:
                    if p[0]&m==p[0] and p[1]&m==m:
                        rt.append(m)
            if set(rt)==set(ttt[:i]):
                pass
                #print 'time: ',z
            else:
                error=True
                print('***************  ERROR  *************************')
                print( 'result=',rt)
        else:
            print( 'no pc')
    if not error:
        print( ':::::::::::::: all correct :::::::::::::::')
    print( 'total time:',time.time()-tz)
