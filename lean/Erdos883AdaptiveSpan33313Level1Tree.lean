import Erdos883AdaptiveSpan33313Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength33313_1 : adaptiveNumericSpans33313_1.length = 482 := by decide +kernel
theorem adaptiveSpanEvenCache33313_1 : adaptiveSpanEven33313_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain33313_1 : adaptiveSpanEven33313_1.domainCheck 16657 = true := by decide +kernel
theorem adaptiveSpanEvenEntries33313_1 : adaptiveSpanEven33313_1.spans = coreEvenSpans 16657 0 adaptiveNumericSpans33313_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache33313_1 : adaptiveSpanWhole33313_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain33313_1 : adaptiveSpanWhole33313_1.domainCheck 16657 = true := by decide +kernel
theorem adaptiveSpanWholeEntries33313_1 : adaptiveSpanWhole33313_1.spans = coreWholeSpans 0 adaptiveNumericSpans33313_1 := by
  decide +kernel
end Erdos883Verified
