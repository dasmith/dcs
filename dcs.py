#!/usr/bin/python
# -*- coding: utf-8 -*-
"""
Dependency-based compositional semantics (DCS)
  - DCS's motivation was "to create a transparent interface between syntax and semantics."
  
References:
    [1] Percy Liang's 2011 PhD Thesis.

"""

import itertools
import inspect
from collections import defaultdict
from geo_db import *

NULL = ('NULL',)

class Relation(object):
    """  A procedure that is applied to two trees """
    pass

class Join(Relation):
    """ Ensures that value of the parent's denotation at parent_index is equal to
    the value of the child's denotation at child_index """

    def __init__(self, parent_index, child_index):
        self.parent_index = parent_index
        self.child_index = child_index

    def __repr__(self):
        return "%i/%i" % (self.parent_index, self.child_index)

    def lambda_formula(self, parent, child):
        return "%s = %s" % (parent, child)


    def __call__(self, parent, child):
        """ Takes a cross product of tuples (the denotations of parent and child)
        and extracts all tuples that match the equality constraint.
        Then it "projects" the results and only takes those up to the parent's arity"""
        # we dont keep stores in the denotation, so we don't have to remove them.
        results = []
        self.twice = True 
        self.once = True
        print "\n\ncalled", parent.predicate,
        if child.denotation is not None: 
            print len(child.denotation)
        else:
            print "Null child"
        print "first c", child.denotation[0]

        def join_function(pc):
            if self.once:
                print pc
                print pc[0][self.parent_index-1], pc[1][self.child_index-1]
                self.once = False
            return pc[0][self.parent_index-1] == pc[1][self.child_index-1]

        def detuple(pc):
            # and de-child
            #if not isinstance(pc[0], tuple):
            #    return tuple(pc[0])# + pc[1]
            return pc[0] #+ pc[1]

        for match in map(detuple, filter(join_function,\
                itertools.product(parent.denotation, child.denotation))):
            # the projection stage -- take the subset of the tuples corresponding
            # to the arity of the parent's predicate
            if self.twice:
                print "MATCH", match
                self.twice = False

            results.append(match)
        
        return results

class Aggregate(Relation):
    """ Sets the parent to all acceptable values of the child.
    
    Takes a subtree and reifies its denotation so that it can be accessed by other nodes.
    
    The aggregation relation sets the parent node to the denotation of the child node.

    Analogous to lambda abstraction.
    """

    def __repr__(self):
        return "\sigma"

    def __call__(self, parent, child):
        # enumerate the child
        print "Called aggregate on", parent.predicate, child.predicate
        return tuple([child.denotation])

class MarkRelation(Relation):
    """ Takes a denotation, d, a mark relation r in [C,Q,E], and a child denotation c
    and sets the store of d in column 1 to be (r, d, c).
    
    Mark allows a node that is lower in the tree to be invoked by a parent tree.
    
    2.4c -- the population node is marked, putting the child argmax is put in a temporary
    store, and then when city is executed, argmax is invoked removed from thes tore and
    invoked.
    
    Denotations are augmented to include information about all marked nodes, since they
    can be accessed by an execute relation."""

    def __init__(self, child_denotation):
        self.child = child_denotation

class Extract(MarkRelation):
    """ Marks the node for extraction """

    def __repr__(self):
        return "E"

class Compare(MarkRelation):
    """ Marks the node for superlative, comparatives """

    def __repr__(self):
        return "C"

class Quantify(MarkRelation):
    """ Marks the node for Quantification, negation """

    def __repr__(self):
        return "Q"

class Execute(Relation):
    """ Processes a marked descendent node and applies it at the desired
    point. """

    def __init__(self, *indices):
        """ Indices is an array of nodes that specifies the order of marked 
        nodes that you want to execute.
        """
        self.indices = indices

    def __repr__(self):
        return "x_i"

    def __call__(self, parent, child):
        print "called execute but i don't know what to do"
        return child.denotation

class DCSTree(object):

    def __init__(self, predicate=None):
        self.predicate = predicate 

        self.arity = 1  # arity of the predicate
        if inspect.isfunction(predicate):
            self.arity = predicate.func_code.co_argcount
        elif inspect.ismethod(predicate):
            # remove self
            self.arity = predicate.func_code.co_argcount - 1 

        # edges is a list of (Relation, DCSTree) tuples
        self.edges = []
        self.denotation = [NULL]
        self.stores = None # for marked nodes

    def add_child(self, relation, child):
        assert isinstance(child, DCSTree)
        assert isinstance(relation, Relation)
        self.edges.append((relation, child,))

    def get_children(self):
        return [child for (_,child)  in self.edges]

    def is_leaf(self):
        return len(self.edges) == 0

    def is_grounded(self):
        return not self.denotation is None

    def ground(self, world=None):
        """
        A denotation consists of n columns, where each column is either the root node
        or a non executed marked node.  Ordered by preorder traversal (self, *children)

        Denotation is a set of arrays, where each is a feasible assignment of values
        to columns.
        
        2.7, there are two columns: one for root state and size, marked by c:

            state, column 1 = OK
            size, column 2 = (TX, 2.7e5)

        If a node is Marked, its denotation also contains a 'store' with information
        to be retrieved when that marked node is executed

        Stores have:
            - the mark relation
            - the base denotation (the denotation of the node excluding the mark relation)[[size]]
            - the denotation of the child of the mark relation [[argmax]]

        """
        # ground all children
        for child in self.get_children():
            child.ground(world)
        
        # ground itself
        print "Grounding ", self.predicate, self.predicate in globals()
        if self.predicate is not None and self.predicate in globals():
            self.denotation = globals()[self.predicate]()
        elif self.predicate is not None:
            c = itertools.chain([c.denotation for c in self.get_children()])
            self.denotation = [entry + (self.predicate(*entry),) for entry in c]
        print "DENOTATION", self.denotation
        if not self.is_grounded():
            raise NotImplemented()
    
        for relation, child in self.edges:
            self.denotation = relation(self, child)

        return self.denotation
    

    def __repr__(self):
        child_string = ":".join(["%s:%s" % (r, c) for r, c in self.edges])
        if child_string:
            return "<%s;%s>" % (self.predicate, child_string)
        else:
            return "<%s>" % (self.predicate)

    def lambda_formula(self, used_symbols=None):
        """ Turns the tree into a lambda expression and returns all of the 
        a list of the terms (strings)
        """
        declarations = []
        dec_type = 'E'

        if used_symbols is None:
            # first call.  top level predicate is a lambda reduction, not an
            # existential quantifier 
            used_symbols = set()
            dec_type = r'\lambda'
            #dec_type = u'λ'

        # perform the alpha-reduction, getting a unique variable name for each
        # predicate
        p, offset = 1, 1
        while True:
            p = "%s%i" % (self.predicate[0].lower(), offset,)
            if p not in used_symbols: break
            offset += 1

        used_symbols.add(p)
        self.p = p
        declarations.append("%s %s " % (dec_type, p))

        for (relation, child) in self.edges:
            declarations += child.lambda_formula(used_symbols)
        # two iterations to keep formulas at the end
        for (relation, child) in self.edges:
            if hasattr(relation, 'lambda_formula'):
                declarations.append(relation.lambda_formula(self.p, child.p))

        return declarations


    @classmethod
    def combine(clz, left_tree, right_tree):
        """ Takes two trees, L and R, and accumulates all combinations of
           (a) L + R with L as root
           (b) L + R with R as root

        All types of relations with relevant arity are considered (e.g. join
        and execute)

        Then trace predicates are considered allowing d-1 additional predicates.
        """
        pass


def count(a):
    return len(a)

def argmax(measure, a):
    return max(a, key=measure)

def argmin(measure, a):
    return min(a, key=measure)

# define generalized quantifiers
# a is restrictor and b is a nuclear scope
def some(a, b):
    return len(a.intersect(b)) > 0

def every(a, b):
    return a.is_subset(b)

def no(a, b):
    return len(a.intersect(b)) == 0

def most(a, b):
    return len(a.intersect(b)) > (0.5 * len(a))


# superlative and comparative
# measure function
def more(measure, a, b):
    return max(measure(a)) > max(measure(b))

def less(measure, a, b):
    return min(measure(a)) < min(measure(b))

#------------------------------------------------------------------------------
# Join function  (Figure 2.2 from [1])
#------------------------------------------------------------------------------
# major cities in ca
def test_join():
    d = DCSTree("city")
    d.add_child(Join(1,1), DCSTree("major"))
    l = DCSTree("loc")
    d.add_child(Join(1,1), l)
    l.add_child(Join(2,1), DCSTree("ca"))
    assert d.ground() == [('los angeles',), ('san diego',), ('san francisco',), ('san jose',)]

#------------------------------------------------------------------------------
# Aggregation function (Page 14)
#------------------------------------------------------------------------------
# number of major cities
r = DCSTree()
ct = DCSTree(count)
agg = DCSTree()
c = DCSTree("city")
r.add_child(Join(1,2), ct)
ct.add_child(Join(1,1), agg)
agg.add_child(Aggregate(), c)
c.add_child(Join(1,1), DCSTree("major"))
print ct.ground()

if False:
    tfb = DCSTree()  # 24 b
    am = DCSTree(argmax)
    tfb.add_child(Join(1,2), am)


    null = DCSTree()
    p= DCSTree("population")
    c = DCSTree("city")
    null.add_child(Aggregate(), p)
    p.add_child(Join(1,1), c)
    print null.ground(1)
#print "CITY", city.ground(1)
#print "POPULATION", population.ground(1)

#------------------------------------------------------------------------------
#------------------------------------------------------------------------------
# state borders state
    null = DCSTree()

    state = DCSTree("state")
    state.denotation = [("AL",), ("AK",), ("CT",)]

    border = DCSTree("border")
    border.denotation = [("FL", "AL"), 
                         ("GA", "AL"),
                         ("MS", "AL"),
                         ("TN", "AL"),]

    state2 = DCSTree("state")
    state2.denotation = [("AL",), ("AK",), ("CT",)]

#null.add_child(Aggregate(), state)
    state.add_child(Join(1,1), border)
    border.add_child(Join(2,1), state2)
    state2.add_child(Execute(), DCSTree())

#print null 
#print null.ground(None)

    print state.ground(None)
