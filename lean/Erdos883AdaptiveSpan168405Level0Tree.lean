import Erdos883AdaptiveSpan168405Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength168405_0 : adaptiveNumericSpans168405_0.length = 746 := by decide +kernel
theorem adaptiveSpanEvenCache168405_0 : adaptiveSpanEven168405_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain168405_0 : adaptiveSpanEven168405_0.domainCheck 84203 = true := by decide +kernel
theorem adaptiveSpanEvenEntries168405_0 : adaptiveSpanEven168405_0.spans = coreEvenSpans 84203 0 adaptiveNumericSpans168405_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache168405_0 : adaptiveSpanWhole168405_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain168405_0 : adaptiveSpanWhole168405_0.domainCheck 84203 = true := by decide +kernel
theorem adaptiveSpanWholeEntries168405_0 : adaptiveSpanWhole168405_0.spans = coreWholeSpans 0 adaptiveNumericSpans168405_0 := by
  decide +kernel
end Erdos883Verified
