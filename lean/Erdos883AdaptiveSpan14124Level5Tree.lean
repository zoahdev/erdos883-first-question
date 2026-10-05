import Erdos883AdaptiveSpan14124Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength14124_5 : adaptiveNumericSpans14124_5.length = 391 := by decide +kernel
theorem adaptiveSpanEvenCache14124_5 : adaptiveSpanEven14124_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain14124_5 : adaptiveSpanEven14124_5.domainCheck 7062 = true := by decide +kernel
theorem adaptiveSpanEvenEntries14124_5 : adaptiveSpanEven14124_5.spans = coreEvenSpans 7062 0 adaptiveNumericSpans14124_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache14124_5 : adaptiveSpanWhole14124_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain14124_5 : adaptiveSpanWhole14124_5.domainCheck 7062 = true := by decide +kernel
theorem adaptiveSpanWholeEntries14124_5 : adaptiveSpanWhole14124_5.spans = coreWholeSpans 0 adaptiveNumericSpans14124_5 := by
  decide +kernel
end Erdos883Verified
