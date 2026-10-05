import Erdos883AdaptiveSpan33313Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength33313_0 : adaptiveNumericSpans33313_0.length = 482 := by decide +kernel
theorem adaptiveSpanEvenCache33313_0 : adaptiveSpanEven33313_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain33313_0 : adaptiveSpanEven33313_0.domainCheck 16657 = true := by decide +kernel
theorem adaptiveSpanEvenEntries33313_0 : adaptiveSpanEven33313_0.spans = coreEvenSpans 16657 0 adaptiveNumericSpans33313_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache33313_0 : adaptiveSpanWhole33313_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain33313_0 : adaptiveSpanWhole33313_0.domainCheck 16657 = true := by decide +kernel
theorem adaptiveSpanWholeEntries33313_0 : adaptiveSpanWhole33313_0.spans = coreWholeSpans 0 adaptiveNumericSpans33313_0 := by
  decide +kernel
end Erdos883Verified
