import Erdos883AdaptiveSpan48777Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength48777_5 : adaptiveNumericSpans48777_5.length = 525 := by decide +kernel
theorem adaptiveSpanEvenCache48777_5 : adaptiveSpanEven48777_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain48777_5 : adaptiveSpanEven48777_5.domainCheck 24389 = true := by decide +kernel
theorem adaptiveSpanEvenEntries48777_5 : adaptiveSpanEven48777_5.spans = coreEvenSpans 24389 0 adaptiveNumericSpans48777_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache48777_5 : adaptiveSpanWhole48777_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain48777_5 : adaptiveSpanWhole48777_5.domainCheck 24389 = true := by decide +kernel
theorem adaptiveSpanWholeEntries48777_5 : adaptiveSpanWhole48777_5.spans = coreWholeSpans 0 adaptiveNumericSpans48777_5 := by
  decide +kernel
end Erdos883Verified
