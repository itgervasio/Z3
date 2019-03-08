from z3 import *
import operator
import exceptions
import copy


class SLA_to_Constraint:
    """Class for preparing a SLA specification and convert it to constraints. 
        It prepares the constraint system and can solve when the monitoring information
        is inputed in the system."""

    def __init__(self, iD, groups, terms, guarantees):
        #use 'soft' constraints (to know which failed)
        self.control_constraints = []
        self.id_of_constraints = 0
        self.solver_SLA = Solver()
        self.iD = iD
        self.terms = terms
        self.groups = groups
        self.guarantees = guarantees
        self.definitions = dict()
        self.constraints_metrics = dict()
        self.instantiated_groups = dict()

    def convert_SLA_to_Constraints(self):
        self.lm_elements = dict()
        self.constraints = dict()
        for group in self.groups:
            if not self._add_group_definition(group, self.definitions):
                return False
        if not self._convert_terms_constraint(self.terms):
            return False
        print self.solver_SLA
        tmp = dict()
        for key,value in sorted(self.constraints.items()):
            tmp [int(key.split('C')[1])] = self.constraints[key]
        for key in sorted(tmp.keys()):
            print 'C',key, '  =  ', tmp[key]
        return True

    def _add_group_definition(self, group, definitions):
        terms =  list()
        for term in group['Terms']:
            if term ['type'] == 'Group':
                term_name = term ['specific']['Metric_Name']
                try:
                    definitions[term_name]
                except exceptions.KeyError:
                    logging.error( 'Error Group not found or not yet defined: ' + term_name)
                    return False
                bounds =  (term['lower_bound'], term ['upper_bound'])
                #Copy, renames and Adds all constraints of the instantiated group  in this group
                for group_number in range (int(bounds[1])):
                    for term_group in definitions[term_name]:
                        copy_term_group = copy.deepcopy (term_group)
                        copy_term_group ['specific'] ['Metric_Name'] = self._generate_Term_Name( term_group, term_name, group_number )
                        terms.append(copy_term_group)
                #Add numeric constraint
                type_interval  = { 'lower' : operator.le, 'upper' : operator.ge }
                group_numeric_metric = { 'Metric_Name' : term['specific']['Metric_Name'], 'Original_Name' : term['specific']['Metric_Name'], 'type_interval' : type_interval, 'bounds' : bounds }
                group_numeric_metric = { 'specific' : group_numeric_metric, 'type' : 'NMG'  }
                terms.append(group_numeric_metric)
            else:
                term['specific'] ['Metric_Name'] = self._generate_Metric_Name(term)
                terms.append(term)
        self.definitions [group['specific']['Metric_Name']] = terms
        return True
               
    def  _add_Group_Constraint(self, group):
        try:
            terms = copy.deepcopy(self.definitions [group['specific']['Metric_Name'] ])
        except:
            index = int(len(group['specific']['Metric_Name'].split(':')) / 2)
            group_name = group['specific']['Metric_Name'].split(':')[index]
            terms = copy.deepcopy(self.definitions [group_name])
        terms_to_convert = list()
        bounds =  (group ['lower_bound'], group ['upper_bound'])
        self.instantiated_groups [group['specific']['Metric_Name']] = bounds[1]
        for group_number in range (int(bounds[1])):
            for term in terms:
                copy_term = copy.deepcopy(term)
                copy_term ['specific']['Metric_Name'] = self._generate_Term_Name(term, group['specific']['Metric_Name'], group_number)
                terms_to_convert.append(copy_term)
        #Add numeric constraint
        type_interval  = { 'lower' : operator.le, 'upper' : operator.ge }
        term_name = group['specific']['Metric_Name'] 
        group_numeric_metric = { 'Metric_Name' : term_name, 'Original_Name' : term_name,  'type_interval' : type_interval, 'bounds' : bounds }
        group_numeric_metric = { 'specific' : group_numeric_metric, 'type' : 'NMG'  }
        terms_to_convert.append(group_numeric_metric)
        self._convert_terms_constraint (terms_to_convert, True)


    def _convert_terms_constraint(self, terms, in_group = False):
        for constraint in terms:
            #Instance of a Group
            if constraint ['type'] == 'Group':
                self._add_Group_Constraint( constraint )

            if not in_group and constraint ['type'] != 'Group':
                constraint['specific']['Metric_Name'] = self._generate_Metric_Name(constraint)

            if constraint ['type'] == 'BM':
                term_id = self._generate_Term_iD(constraint)
                self._add_BM( constraint ['specific'], term_id )

            elif constraint ['type'] == 'LM':
                term_id = self._generate_Term_iD(constraint)
                self._add_LM( constraint ['specific'], term_id )

            elif constraint ['type'] == 'NM' or constraint ['type'] == 'NMG' :
                term_id = self._generate_Term_iD(constraint)
                self._add_NM( constraint ['specific'], term_id )
        return True

    def _generate_Term_Name(self, constraint, group_name = None, group_number = None):
        name = group_name + ':' +  constraint['specific'] ['Metric_Name'] + ':' + str(group_number)
        return name

    def _generate_Metric_Name(self, constraint):
        if constraint['type'] == 'NMG':
            return constraint ['specific']['Metric_Name']
        parties = ''
        for party in constraint ['Destination_Parties']:
            if parties == '':
                parties = party.strip()
            else:
                parties += ','+party.strip()
        name = constraint [ 'Source_Party' ] + ':' + parties + ':' +  constraint['specific'] ['Metric_Name']
        return name

    def _generate_Term_iD(self, constraint):
        self.id_of_constraints += 1
        key = 'C'+str(self.id_of_constraints)
        self.constraints[ key ] =  constraint ['specific'] ['Metric_Name']
        self.constraints_metrics[ key ] =  constraint ['specific'] ['Original_Name']
        return key

    def _add_NM(self, constraint, term_id):
        metric_control = Bool(str(term_id)+':Control')
        self.control_constraints.append( metric_control )
        lower_operator = constraint ['type_interval']['lower']
        upper_operator = constraint ['type_interval']['upper']
        lower_bound = constraint ['bounds'][0]
        upper_bound = constraint ['bounds'][1]

        try:
            if lower_bound:
                lower_bound = float ( lower_bound )
            if upper_bound:
                upper_bound = float ( upper_bound )
            metric = Real(term_id)

        except exceptions.ValueError:
            logging.error('Error of value in the NM: ', name, 'Value could not be coverted to Real in SLA: '+ self.iD)

        if not lower_bound:
                #No lower bound, add only upperbound
                self.solver_SLA.add(Implies(metric_control, upper_operator(upper_bound, metric) ))
        elif not upper_bound:
                #the opposite
                self.solver_SLA.add( Implies(metric_control, lower_operator(lower_bound, metric) ))
        else:
                #Add both
                self.solver_SLA.add( Implies(metric_control, upper_operator(upper_bound, metric) ))
                self.solver_SLA.add( Implies(metric_control, lower_operator(lower_bound, metric) ))


    def _add_BM(self, constraint, term_id):
        metric = Bool(term_id)
        metric_control = Bool(str(term_id)+':Control')
        self.control_constraints.append( metric_control )
        self.solver_SLA.add( Implies( metric_control, metric == constraint ['Boolean'] ))
        #Add monitoring variable to compare the SLA boolean with the monitoring result
        #Tried without but did not work
        monitoring_metric = Bool(str(term_id)+':monitoring')
        self.solver_SLA.add( Implies( metric_control, metric == monitoring_metric ))

    def _add_LM(self, constraint, term_id):
        metric_control = Bool(str(term_id)+':Control')
        self.control_constraints.append( metric_control )
        list_lm = []
        for k, list_elements in enumerate(constraint [ 'List_Elements']):
            list_and = [Bool(str(term_id)+':E'+str(k)+':'+element) for element in list_elements] 
            for x in list_and:
                self.lm_elements [ str(x) ] = x
            list_and = And(list_and)
            list_lm.append(list_and)
        self.solver_SLA.add( Implies( metric_control, Or ( list_lm )))
