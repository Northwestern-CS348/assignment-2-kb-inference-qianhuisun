import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here

        if isinstance(fact_or_rule, Fact):
            if not fact_or_rule in self.facts:
                return
            fact_to_remove = self.facts[self.facts.index(fact_or_rule)]
            if not fact_to_remove.supported_by:
                if fact_to_remove.asserted:
                    fact_to_remove.asserted = False
                for fact in fact_to_remove.supports_facts:
                    fact_to_retract = self.facts[self.facts.index(fact)]
                    for x in fact_to_retract.supported_by[:]:
                        if fact_to_remove in x:
                            fact_to_retract.supported_by.remove(x)
                    if not fact_to_retract.asserted:
                        self.kb_retract(fact_to_retract)
                for rule in fact_to_remove.supports_rules:
                    rule_to_retract = self.rules[self.rules.index(rule)]
                    for x in rule_to_retract.supported_by[:]:
                        if fact_to_remove in x:
                            rule_to_retract.supported_by.remove(x)
                    if not rule_to_retract.asserted:
                        self.kb_retract(rule_to_retract)
                self.facts.remove(fact_to_remove)

        elif isinstance(fact_or_rule, Rule):
            if not fact_or_rule in self.rules:
                return
            rule_to_remove = self.rules[self.rules.index(fact_or_rule)]
            if not rule_to_remove.supported_by and not rule_to_remove.asserted:
                for fact in rule_to_remove.supports_facts:
                    fact_to_retract = self.facts[self.facts.index(fact)]
                    for x in fact_to_retract.supported_by[:]:
                        if rule_to_remove in x:
                            fact_to_retract.supported_by.remove(x)
                    if not fact_to_retract.asserted:
                        self.kb_retract(fact_to_retract)
                for rule in rule_to_remove.supports_rules:
                    rule_to_retract = self.rules[self.rules.index(rule)]
                    for x in rule_to_retract.supported_by[:]:
                        if rule_to_remove in x:
                            rule_to_retract.supported_by.remove(x)
                    if not rule_to_retract.asserted:
                        self.kb_retract(rule_to_retract)
                self.rules.remove(rule_to_remove)


class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        
        bindings = match(fact.statement, rule.lhs[0])
        # if fact and rule match, then we have bindings to be True
        if bindings:
            if len(rule.lhs) == 1:
                # At first, use deepcopy and change the predicate and terms.
                # Now use instantiate instead. 
                # In this way, create a statement and link its predicate and terms to original statement. 
                outcome_fact = Fact(instantiate(rule.rhs, bindings), [[fact, rule]])
                """
                rule_cp = copy.deepcopy(rule)
                outcome_fact = Fact(rule_cp.rhs, [[fact, rule]])
                for term in outcome_fact.statement.terms:
                    if term.term.element in bindings.bindings_dict:
                        ind = outcome_fact.statement.terms.index(term)
                        outcome_fact.statement.terms[ind].term = Constant(bindings.bindings_dict[term.term.element])
                """
                fact.supports_facts.append(outcome_fact)
                rule.supports_facts.append(outcome_fact)
                kb.kb_add(outcome_fact)
            else:
                outcome_rule = Rule([[instantiate(state_lhs, bindings) for state_lhs in rule.lhs[1:]], instantiate(rule.rhs, bindings)], [[fact, rule]])
                # At first, use deepcopy and change the predicate and terms.
                # Now use instantiate instead. 
                # In this way, create a statement and link its predicate and terms to original statement. 
                """
                rule_cp = copy.deepcopy(rule)
                outcome_rule = Rule([rule_cp.lhs[1:], rule_cp.rhs], [[fact, rule]])
                for lhs_statement in outcome_rule.lhs:
                    for term in lhs_statement.terms:
                        if term.term.element in bindings.bindings_dict:
                            ind = lhs_statement.terms.index(term)
                            lhs_statement.terms[ind].term = Constant(bindings.bindings_dict[term.term.element])
                for term in outcome_rule.rhs.terms:
                    if term.term.element in bindings.bindings_dict:
                        ind = outcome_rule.rhs.terms.index(term)
                        outcome_rule.rhs.terms[ind].term = Constant(bindings.bindings_dict[term.term.element])
                """
                fact.supports_rules.append(outcome_rule)
                rule.supports_rules.append(outcome_rule)
                kb.kb_add(outcome_rule)

