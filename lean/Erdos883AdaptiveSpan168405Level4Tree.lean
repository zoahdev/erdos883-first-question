import Erdos883AdaptiveSpan168405Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength168405_4 : adaptiveNumericSpans168405_4.length = 746 := by decide +kernel
theorem adaptiveSpanEvenCache168405_4 : adaptiveSpanEven168405_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain168405_4 : adaptiveSpanEven168405_4.domainCheck 84203 = true := by decide +kernel
theorem adaptiveSpanEvenEntries168405_4 : adaptiveSpanEven168405_4.spans = coreEvenSpans 84203 0 adaptiveNumericSpans168405_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache168405_4 : adaptiveSpanWhole168405_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain168405_4 : adaptiveSpanWhole168405_4.domainCheck 84203 = true := by decide +kernel
theorem adaptiveSpanWholeEntries168405_4 : adaptiveSpanWhole168405_4.spans = coreWholeSpans 0 adaptiveNumericSpans168405_4 := by
  decide +kernel
end Erdos883Verified
