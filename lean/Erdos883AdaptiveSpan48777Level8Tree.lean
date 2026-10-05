import Erdos883AdaptiveSpan48777Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength48777_8 : adaptiveNumericSpans48777_8.length = 527 := by decide +kernel
theorem adaptiveSpanEvenCache48777_8 : adaptiveSpanEven48777_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain48777_8 : adaptiveSpanEven48777_8.domainCheck 24389 = true := by decide +kernel
theorem adaptiveSpanEvenEntries48777_8 : adaptiveSpanEven48777_8.spans = coreEvenSpans 24389 0 adaptiveNumericSpans48777_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache48777_8 : adaptiveSpanWhole48777_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain48777_8 : adaptiveSpanWhole48777_8.domainCheck 24389 = true := by decide +kernel
theorem adaptiveSpanWholeEntries48777_8 : adaptiveSpanWhole48777_8.spans = coreWholeSpans 0 adaptiveNumericSpans48777_8 := by
  decide +kernel
end Erdos883Verified
