import Erdos883AdaptiveSpan14124Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength14124_6 : adaptiveNumericSpans14124_6.length = 391 := by decide +kernel
theorem adaptiveSpanEvenCache14124_6 : adaptiveSpanEven14124_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain14124_6 : adaptiveSpanEven14124_6.domainCheck 7062 = true := by decide +kernel
theorem adaptiveSpanEvenEntries14124_6 : adaptiveSpanEven14124_6.spans = coreEvenSpans 7062 0 adaptiveNumericSpans14124_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache14124_6 : adaptiveSpanWhole14124_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain14124_6 : adaptiveSpanWhole14124_6.domainCheck 7062 = true := by decide +kernel
theorem adaptiveSpanWholeEntries14124_6 : adaptiveSpanWhole14124_6.spans = coreWholeSpans 0 adaptiveNumericSpans14124_6 := by
  decide +kernel
end Erdos883Verified
