from z3 import *
import operator
import exceptions

class Monitoring_to_Constraint:
    """Class for preparing and converting the monitoring data to constraints. """

    def __init__(self, iD, metrics, lm_elements):
        #TODO remove lm_elements, find a way to set all LM constraints that are not in the monitoring list as false
        self.solver_Monitoring = Solver()
        self.lm_elements = lm_elements
        self.iD = iD
        self.metrics = metrics
        self._add_constraints(metrics)

    def _add_constraints(self, metrics):
        for metric in metrics:
            if metric ['type'] == 'NM':
                self._add_NM(metric ['Metric_Name'], metric['Value'])

            elif metric['type'] == 'BM':
                self._add_BM(metric ['Metric_Name'], metric['Value'])

            elif metric['type'] == 'LM':
                self._add_LM(metric ['Metric_Name'], metric['Value'])

    def _add_NM(self, name, value):
        metric_control = Bool(name+':Control')
        try:
            value = float(value)
            metric = Real(name)
        except exceptions.ValueError:
            print 'Error of value in the NM: ', name
            print 'Value could not be coverted to Real'
        self.solver_Monitoring.add( Implies(metric_control, operator.eq(metric, value) ))

    def _add_BM(self, name, boolean):
        metric_control = Bool(name+':Control')
        name = name+':monitoring'
        metric = Bool(name)
        self.solver_Monitoring.add( Implies( metric_control, operator.eq(metric, boolean) ) )

    def _add_LM(self, name, values):
        metric_control = Bool(name+':Control')
        for element in self.lm_elements:
            used = False
            for value in values: 
                if value in element:
                    used = True
                    element_constraint = Bool(element)
                    self.solver_Monitoring.add( Implies( metric_control, element_constraint == True ) )
            if not used:
                    element_constraint = Bool(element)
                    self.solver_Monitoring.add( Implies( metric_control, element_constraint == False) )
