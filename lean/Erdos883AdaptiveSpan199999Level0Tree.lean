import Erdos883AdaptiveSpan199999Level0TreeData
import Erdos883AdaptiveSpanCompact
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength199999_0 : adaptiveNumericSpans199999_0.length = 782 := by decide +kernel
theorem adaptiveSpanEvenCache199999_0 : adaptiveSpanEven199999_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain199999_0 : adaptiveSpanEven199999_0.domainCheck 100000 = true := by decide +kernel
theorem adaptiveSpanEvenEntries199999_0 : adaptiveSpanEven199999_0.spans = coreEvenSpans 100000 0 adaptiveNumericSpans199999_0 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreEvenSpans_length, adaptiveNumericSpansLength199999_0]
  decide
theorem adaptiveSpanWholeCache199999_0 : adaptiveSpanWhole199999_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain199999_0 : adaptiveSpanWhole199999_0.domainCheck 100000 = true := by decide +kernel
theorem adaptiveSpanWholeEntries199999_0 : adaptiveSpanWhole199999_0.spans = coreWholeSpans 0 adaptiveNumericSpans199999_0 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreWholeSpans_length, adaptiveNumericSpansLength199999_0]
  decide
end Erdos883Verified
