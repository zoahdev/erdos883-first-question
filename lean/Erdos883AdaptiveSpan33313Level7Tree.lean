import Erdos883AdaptiveSpan33313Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength33313_7 : adaptiveNumericSpans33313_7.length = 482 := by decide +kernel
theorem adaptiveSpanEvenCache33313_7 : adaptiveSpanEven33313_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain33313_7 : adaptiveSpanEven33313_7.domainCheck 16657 = true := by decide +kernel
theorem adaptiveSpanEvenEntries33313_7 : adaptiveSpanEven33313_7.spans = coreEvenSpans 16657 0 adaptiveNumericSpans33313_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache33313_7 : adaptiveSpanWhole33313_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain33313_7 : adaptiveSpanWhole33313_7.domainCheck 16657 = true := by decide +kernel
theorem adaptiveSpanWholeEntries33313_7 : adaptiveSpanWhole33313_7.spans = coreWholeSpans 0 adaptiveNumericSpans33313_7 := by
  decide +kernel
end Erdos883Verified
