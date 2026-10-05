import Erdos883AdaptiveSpan199999Level1TreeData
import Erdos883AdaptiveSpanCompact
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength199999_1 : adaptiveNumericSpans199999_1.length = 782 := by decide +kernel
theorem adaptiveSpanEvenCache199999_1 : adaptiveSpanEven199999_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain199999_1 : adaptiveSpanEven199999_1.domainCheck 100000 = true := by decide +kernel
theorem adaptiveSpanEvenEntries199999_1 : adaptiveSpanEven199999_1.spans = coreEvenSpans 100000 0 adaptiveNumericSpans199999_1 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreEvenSpans_length, adaptiveNumericSpansLength199999_1]
  decide
theorem adaptiveSpanWholeCache199999_1 : adaptiveSpanWhole199999_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain199999_1 : adaptiveSpanWhole199999_1.domainCheck 100000 = true := by decide +kernel
theorem adaptiveSpanWholeEntries199999_1 : adaptiveSpanWhole199999_1.spans = coreWholeSpans 0 adaptiveNumericSpans199999_1 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreWholeSpans_length, adaptiveNumericSpansLength199999_1]
  decide
end Erdos883Verified
