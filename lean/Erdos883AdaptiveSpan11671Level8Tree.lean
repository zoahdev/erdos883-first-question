import Erdos883AdaptiveSpan11671Level8TreeData
import Erdos883AdaptiveSpanCompact
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength11671_8 : adaptiveNumericSpans11671_8.length = 375 := by decide +kernel
theorem adaptiveSpanEvenCache11671_8 : adaptiveSpanEven11671_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain11671_8 : adaptiveSpanEven11671_8.domainCheck 5836 = true := by decide +kernel
theorem adaptiveSpanEvenEntries11671_8 : adaptiveSpanEven11671_8.spans = coreEvenSpans 5836 0 adaptiveNumericSpans11671_8 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreEvenSpans_length, adaptiveNumericSpansLength11671_8]
  decide
theorem adaptiveSpanWholeCache11671_8 : adaptiveSpanWhole11671_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain11671_8 : adaptiveSpanWhole11671_8.domainCheck 5836 = true := by decide +kernel
theorem adaptiveSpanWholeEntries11671_8 : adaptiveSpanWhole11671_8.spans = coreWholeSpans 0 adaptiveNumericSpans11671_8 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreWholeSpans_length, adaptiveNumericSpansLength11671_8]
  decide
end Erdos883Verified
