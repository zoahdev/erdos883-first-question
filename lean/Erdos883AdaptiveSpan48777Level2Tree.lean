import Erdos883AdaptiveSpan48777Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength48777_2 : adaptiveNumericSpans48777_2.length = 525 := by decide +kernel
theorem adaptiveSpanEvenCache48777_2 : adaptiveSpanEven48777_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain48777_2 : adaptiveSpanEven48777_2.domainCheck 24389 = true := by decide +kernel
theorem adaptiveSpanEvenEntries48777_2 : adaptiveSpanEven48777_2.spans = coreEvenSpans 24389 0 adaptiveNumericSpans48777_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache48777_2 : adaptiveSpanWhole48777_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain48777_2 : adaptiveSpanWhole48777_2.domainCheck 24389 = true := by decide +kernel
theorem adaptiveSpanWholeEntries48777_2 : adaptiveSpanWhole48777_2.spans = coreWholeSpans 0 adaptiveNumericSpans48777_2 := by
  decide +kernel
end Erdos883Verified
