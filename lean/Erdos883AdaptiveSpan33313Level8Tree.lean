import Erdos883AdaptiveSpan33313Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength33313_8 : adaptiveNumericSpans33313_8.length = 482 := by decide +kernel
theorem adaptiveSpanEvenCache33313_8 : adaptiveSpanEven33313_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain33313_8 : adaptiveSpanEven33313_8.domainCheck 16657 = true := by decide +kernel
theorem adaptiveSpanEvenEntries33313_8 : adaptiveSpanEven33313_8.spans = coreEvenSpans 16657 0 adaptiveNumericSpans33313_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache33313_8 : adaptiveSpanWhole33313_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain33313_8 : adaptiveSpanWhole33313_8.domainCheck 16657 = true := by decide +kernel
theorem adaptiveSpanWholeEntries33313_8 : adaptiveSpanWhole33313_8.spans = coreWholeSpans 0 adaptiveNumericSpans33313_8 := by
  decide +kernel
end Erdos883Verified
