import Erdos883AdaptiveSpan10609Level5TreeData
import Erdos883AdaptiveSpanCompact
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength10609_5 : adaptiveNumericSpans10609_5.length = 364 := by decide +kernel
theorem adaptiveSpanEvenCache10609_5 : adaptiveSpanEven10609_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain10609_5 : adaptiveSpanEven10609_5.domainCheck 5305 = true := by decide +kernel
theorem adaptiveSpanEvenEntries10609_5 : adaptiveSpanEven10609_5.spans = coreEvenSpans 5305 0 adaptiveNumericSpans10609_5 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreEvenSpans_length, adaptiveNumericSpansLength10609_5]
  decide
theorem adaptiveSpanWholeCache10609_5 : adaptiveSpanWhole10609_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain10609_5 : adaptiveSpanWhole10609_5.domainCheck 5305 = true := by decide +kernel
theorem adaptiveSpanWholeEntries10609_5 : adaptiveSpanWhole10609_5.spans = coreWholeSpans 0 adaptiveNumericSpans10609_5 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreWholeSpans_length, adaptiveNumericSpansLength10609_5]
  decide
end Erdos883Verified
