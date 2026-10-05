import Erdos883AdaptiveSpan33313Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength33313_4 : adaptiveNumericSpans33313_4.length = 482 := by decide +kernel
theorem adaptiveSpanEvenCache33313_4 : adaptiveSpanEven33313_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain33313_4 : adaptiveSpanEven33313_4.domainCheck 16657 = true := by decide +kernel
theorem adaptiveSpanEvenEntries33313_4 : adaptiveSpanEven33313_4.spans = coreEvenSpans 16657 0 adaptiveNumericSpans33313_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache33313_4 : adaptiveSpanWhole33313_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain33313_4 : adaptiveSpanWhole33313_4.domainCheck 16657 = true := by decide +kernel
theorem adaptiveSpanWholeEntries33313_4 : adaptiveSpanWhole33313_4.spans = coreWholeSpans 0 adaptiveNumericSpans33313_4 := by
  decide +kernel
end Erdos883Verified
