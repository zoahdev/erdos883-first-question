import Erdos883AdaptiveSpan168405Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength168405_2 : adaptiveNumericSpans168405_2.length = 746 := by decide +kernel
theorem adaptiveSpanEvenCache168405_2 : adaptiveSpanEven168405_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain168405_2 : adaptiveSpanEven168405_2.domainCheck 84203 = true := by decide +kernel
theorem adaptiveSpanEvenEntries168405_2 : adaptiveSpanEven168405_2.spans = coreEvenSpans 84203 0 adaptiveNumericSpans168405_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache168405_2 : adaptiveSpanWhole168405_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain168405_2 : adaptiveSpanWhole168405_2.domainCheck 84203 = true := by decide +kernel
theorem adaptiveSpanWholeEntries168405_2 : adaptiveSpanWhole168405_2.spans = coreWholeSpans 0 adaptiveNumericSpans168405_2 := by
  decide +kernel
end Erdos883Verified
