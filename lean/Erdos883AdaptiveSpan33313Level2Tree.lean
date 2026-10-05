import Erdos883AdaptiveSpan33313Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength33313_2 : adaptiveNumericSpans33313_2.length = 482 := by decide +kernel
theorem adaptiveSpanEvenCache33313_2 : adaptiveSpanEven33313_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain33313_2 : adaptiveSpanEven33313_2.domainCheck 16657 = true := by decide +kernel
theorem adaptiveSpanEvenEntries33313_2 : adaptiveSpanEven33313_2.spans = coreEvenSpans 16657 0 adaptiveNumericSpans33313_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache33313_2 : adaptiveSpanWhole33313_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain33313_2 : adaptiveSpanWhole33313_2.domainCheck 16657 = true := by decide +kernel
theorem adaptiveSpanWholeEntries33313_2 : adaptiveSpanWhole33313_2.spans = coreWholeSpans 0 adaptiveNumericSpans33313_2 := by
  decide +kernel
end Erdos883Verified
