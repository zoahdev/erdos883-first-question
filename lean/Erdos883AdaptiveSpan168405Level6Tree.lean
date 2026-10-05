import Erdos883AdaptiveSpan168405Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength168405_6 : adaptiveNumericSpans168405_6.length = 746 := by decide +kernel
theorem adaptiveSpanEvenCache168405_6 : adaptiveSpanEven168405_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain168405_6 : adaptiveSpanEven168405_6.domainCheck 84203 = true := by decide +kernel
theorem adaptiveSpanEvenEntries168405_6 : adaptiveSpanEven168405_6.spans = coreEvenSpans 84203 0 adaptiveNumericSpans168405_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache168405_6 : adaptiveSpanWhole168405_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain168405_6 : adaptiveSpanWhole168405_6.domainCheck 84203 = true := by decide +kernel
theorem adaptiveSpanWholeEntries168405_6 : adaptiveSpanWhole168405_6.spans = coreWholeSpans 0 adaptiveNumericSpans168405_6 := by
  decide +kernel
end Erdos883Verified
