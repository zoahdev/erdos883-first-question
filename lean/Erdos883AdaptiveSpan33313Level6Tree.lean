import Erdos883AdaptiveSpan33313Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength33313_6 : adaptiveNumericSpans33313_6.length = 482 := by decide +kernel
theorem adaptiveSpanEvenCache33313_6 : adaptiveSpanEven33313_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain33313_6 : adaptiveSpanEven33313_6.domainCheck 16657 = true := by decide +kernel
theorem adaptiveSpanEvenEntries33313_6 : adaptiveSpanEven33313_6.spans = coreEvenSpans 16657 0 adaptiveNumericSpans33313_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache33313_6 : adaptiveSpanWhole33313_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain33313_6 : adaptiveSpanWhole33313_6.domainCheck 16657 = true := by decide +kernel
theorem adaptiveSpanWholeEntries33313_6 : adaptiveSpanWhole33313_6.spans = coreWholeSpans 0 adaptiveNumericSpans33313_6 := by
  decide +kernel
end Erdos883Verified
