import Erdos883AdaptiveSpan64924Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength64924_7 : adaptiveNumericSpans64924_7.length = 567 := by decide +kernel
theorem adaptiveSpanEvenCache64924_7 : adaptiveSpanEven64924_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain64924_7 : adaptiveSpanEven64924_7.domainCheck 32462 = true := by decide +kernel
theorem adaptiveSpanEvenEntries64924_7 : adaptiveSpanEven64924_7.spans = coreEvenSpans 32462 0 adaptiveNumericSpans64924_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache64924_7 : adaptiveSpanWhole64924_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain64924_7 : adaptiveSpanWhole64924_7.domainCheck 32462 = true := by decide +kernel
theorem adaptiveSpanWholeEntries64924_7 : adaptiveSpanWhole64924_7.spans = coreWholeSpans 0 adaptiveNumericSpans64924_7 := by
  decide +kernel
end Erdos883Verified
