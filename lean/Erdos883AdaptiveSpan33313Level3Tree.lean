import Erdos883AdaptiveSpan33313Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength33313_3 : adaptiveNumericSpans33313_3.length = 482 := by decide +kernel
theorem adaptiveSpanEvenCache33313_3 : adaptiveSpanEven33313_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain33313_3 : adaptiveSpanEven33313_3.domainCheck 16657 = true := by decide +kernel
theorem adaptiveSpanEvenEntries33313_3 : adaptiveSpanEven33313_3.spans = coreEvenSpans 16657 0 adaptiveNumericSpans33313_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache33313_3 : adaptiveSpanWhole33313_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain33313_3 : adaptiveSpanWhole33313_3.domainCheck 16657 = true := by decide +kernel
theorem adaptiveSpanWholeEntries33313_3 : adaptiveSpanWhole33313_3.spans = coreWholeSpans 0 adaptiveNumericSpans33313_3 := by
  decide +kernel
end Erdos883Verified
