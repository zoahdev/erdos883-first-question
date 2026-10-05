import Erdos883AdaptiveSpan33313Level9TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength33313_9 : adaptiveNumericSpans33313_9.length = 482 := by decide +kernel
theorem adaptiveSpanEvenCache33313_9 : adaptiveSpanEven33313_9.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain33313_9 : adaptiveSpanEven33313_9.domainCheck 16657 = true := by decide +kernel
theorem adaptiveSpanEvenEntries33313_9 : adaptiveSpanEven33313_9.spans = coreEvenSpans 16657 0 adaptiveNumericSpans33313_9 := by
  decide +kernel
theorem adaptiveSpanWholeCache33313_9 : adaptiveSpanWhole33313_9.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain33313_9 : adaptiveSpanWhole33313_9.domainCheck 16657 = true := by decide +kernel
theorem adaptiveSpanWholeEntries33313_9 : adaptiveSpanWhole33313_9.spans = coreWholeSpans 0 adaptiveNumericSpans33313_9 := by
  decide +kernel
end Erdos883Verified
