onmessage=event=>{const message=event.data;postMessage({protocol:1,type:'started',generation:message.generation,id:message.id});for(;;){}};
