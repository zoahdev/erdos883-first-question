import Erdos883AdaptiveSpan33313Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength33313_5 : adaptiveNumericSpans33313_5.length = 482 := by decide +kernel
theorem adaptiveSpanEvenCache33313_5 : adaptiveSpanEven33313_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain33313_5 : adaptiveSpanEven33313_5.domainCheck 16657 = true := by decide +kernel
theorem adaptiveSpanEvenEntries33313_5 : adaptiveSpanEven33313_5.spans = coreEvenSpans 16657 0 adaptiveNumericSpans33313_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache33313_5 : adaptiveSpanWhole33313_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain33313_5 : adaptiveSpanWhole33313_5.domainCheck 16657 = true := by decide +kernel
theorem adaptiveSpanWholeEntries33313_5 : adaptiveSpanWhole33313_5.spans = coreWholeSpans 0 adaptiveNumericSpans33313_5 := by
  decide +kernel
end Erdos883Verified
