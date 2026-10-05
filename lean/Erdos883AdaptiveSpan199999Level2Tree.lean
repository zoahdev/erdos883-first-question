import Erdos883AdaptiveSpan199999Level2TreeData
import Erdos883AdaptiveSpanCompact
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength199999_2 : adaptiveNumericSpans199999_2.length = 782 := by decide +kernel
theorem adaptiveSpanEvenCache199999_2 : adaptiveSpanEven199999_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain199999_2 : adaptiveSpanEven199999_2.domainCheck 100000 = true := by decide +kernel
theorem adaptiveSpanEvenEntries199999_2 : adaptiveSpanEven199999_2.spans = coreEvenSpans 100000 0 adaptiveNumericSpans199999_2 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreEvenSpans_length, adaptiveNumericSpansLength199999_2]
  decide
theorem adaptiveSpanWholeCache199999_2 : adaptiveSpanWhole199999_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain199999_2 : adaptiveSpanWhole199999_2.domainCheck 100000 = true := by decide +kernel
theorem adaptiveSpanWholeEntries199999_2 : adaptiveSpanWhole199999_2.spans = coreWholeSpans 0 adaptiveNumericSpans199999_2 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreWholeSpans_length, adaptiveNumericSpansLength199999_2]
  decide
end Erdos883Verified
