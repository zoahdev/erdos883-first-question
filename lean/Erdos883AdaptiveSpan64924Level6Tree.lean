import Erdos883AdaptiveSpan64924Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength64924_6 : adaptiveNumericSpans64924_6.length = 567 := by decide +kernel
theorem adaptiveSpanEvenCache64924_6 : adaptiveSpanEven64924_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain64924_6 : adaptiveSpanEven64924_6.domainCheck 32462 = true := by decide +kernel
theorem adaptiveSpanEvenEntries64924_6 : adaptiveSpanEven64924_6.spans = coreEvenSpans 32462 0 adaptiveNumericSpans64924_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache64924_6 : adaptiveSpanWhole64924_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain64924_6 : adaptiveSpanWhole64924_6.domainCheck 32462 = true := by decide +kernel
theorem adaptiveSpanWholeEntries64924_6 : adaptiveSpanWhole64924_6.spans = coreWholeSpans 0 adaptiveNumericSpans64924_6 := by
  decide +kernel
end Erdos883Verified
