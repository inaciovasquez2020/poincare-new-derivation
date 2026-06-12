import Regge.DSQMetricValidityInputSurface
import Regge.DSQConcreteMetricValidityPredicate

namespace Regge

def DSQConcreteMetricValidityPredicate_to_DSQMetricValidityInputSurface
    (p : DSQConcreteMetricValidityPredicate) :
    DSQMetricValidityInputSurface :=
  p.target.surface

end Regge
